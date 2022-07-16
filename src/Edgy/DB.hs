{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Edgy.DB
  ( DB,
    openDB,
    closeDB,
    DBRef,
    DBStorable (..),
    getDBRef,
    readDBRef,
    writeDBRef,
    delDBRef,
    Persister (..),
    filePersister,
  )
where

import Control.Concurrent
  ( MVar,
    forkIO,
    newEmptyMVar,
    newMVar,
    putMVar,
    takeMVar,
    withMVar,
  )
import Control.Concurrent.STM
  ( STM,
    TVar,
    atomically,
    newTVar,
    newTVarIO,
    readTVar,
    retry,
    writeTVar,
  )
import Control.Monad (forM_, when)
import Control.Monad.Extra (whileM)
import Data.Binary (decode, encode)
import Data.Bool (bool)
import qualified Data.ByteString as BS
import Data.ByteString.Lazy (ByteString)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import Data.Typeable (TypeRep, Typeable, typeRep)
import qualified Focus
import GHC.Conc (unsafeIOToSTM)
import qualified StmContainers.Map as SMap
import System.Directory (createDirectoryIfMissing, doesFileExist, removeFile)
import System.FilePath ((</>))
import System.Mem.Weak (Weak, addFinalizer, deRefWeak, mkWeak)
import Unsafe.Coerce (unsafeCoerce)

class Typeable a => DBStorable a where
  getDB :: DB -> ByteString -> STM a
  putDB :: a -> ByteString

data Possible a = Loading | Missing | Present a

data SomeTVar = forall a. DBStorable a => SomeTVar (TVar (Possible a))

data Persister
  = Persister
      (String -> IO (Maybe ByteString))
      (Map String (Maybe ByteString) -> IO ())

data DB = DB
  { dbRefs :: SMap.Map String (TypeRep, Weak SomeTVar),
    dbDirty :: TVar (Map String (SomeTVar, Maybe ByteString)),
    dbPersister :: Persister,
    dbClosing :: TVar Bool,
    dbClosed :: TVar Bool
  }

data DBRef a = DBRef DB String (TVar (Possible a))

instance Eq (DBRef a) where
  DBRef _ k1 _ == DBRef _ k2 _ = k1 == k2

instance Ord (DBRef a) where
  compare (DBRef _ k1 _) (DBRef _ k2 _) = compare k1 k2

instance Show (DBRef a) where
  show (DBRef _ s _) = s

instance DBStorable a => DBStorable (DBRef a) where
  getDB db bs = getDBRef db (decode bs)
  putDB (DBRef _ dbkey _) = encode dbkey

filePersister :: FilePath -> IO Persister
filePersister dir = do
  createDirectoryIfMissing True dir
  lock <- newMVar ()
  return $
    Persister
      ( \key -> withMVar lock $ \_ -> do
          ex <- doesFileExist (dir </> key)
          if ex
            then Just <$> BS.fromStrict <$> BS.readFile (dir </> key)
            else return Nothing
      )
      ( \m -> withMVar lock $ \_ -> forM_ (Map.toList m) $
          \(key, mbs) -> case mbs of
            Just bs -> BS.writeFile (dir </> key) (BS.toStrict bs)
            Nothing -> removeFile (dir </> key)
      )

openDB :: Persister -> IO DB
openDB persister@(Persister _ writer) = do
  refs <- SMap.newIO
  dirty <- newTVarIO Map.empty
  closing <- newTVarIO False
  closed <- newTVarIO False
  _ <- forkIO $ do
    whileM $ do
      (d, c) <- atomically $ do
        c <- readTVar closing
        d <- readTVar dirty
        when (not c && Map.null d) retry
        when (not (Map.null d)) $ writeTVar dirty Map.empty
        return (d, c)
      when (not (Map.null d)) $ writer (snd <$> d)
      return (not c)
    atomically $ writeTVar closed True
  let db =
        DB
          { dbRefs = refs,
            dbDirty = dirty,
            dbPersister = persister,
            dbClosing = closing,
            dbClosed = closed
          }
  return db

closeDB :: DB -> IO ()
closeDB db = do
  atomically $ writeTVar (dbClosing db) True
  atomically $ readTVar (dbClosed db) >>= bool retry (return ())

readForDB :: DBStorable a => DB -> String -> MVar (Possible a) -> IO ()
readForDB db key mvar = do
  let (Persister reader _) = dbPersister db
  readResult <- reader key
  case readResult of
    Just bs -> do
      v <- atomically (getDB db bs)
      putMVar mvar (Present v)
    Nothing -> putMVar mvar Missing

getDBRef :: forall a. DBStorable a => DB -> String -> STM (DBRef a)
getDBRef db key =
  SMap.lookup key (dbRefs db) >>= \case
    Just (tr, weakRef)
      | tr == typeRep (Proxy @a) ->
          unsafeIOToSTM (deRefWeak weakRef) >>= \case
            Just (SomeTVar ref) -> return (DBRef db key (unsafeCoerce ref))
            Nothing -> insert
      | otherwise -> error "Type mismatch in DBRef"
    Nothing -> insert
  where
    insert = do
      ref <- newTVar Loading
      ptr <- unsafeIOToSTM $ do
        ptr <- mkWeak ref (SomeTVar ref) Nothing
        addFinalizer ref $
          atomically $
            SMap.focus
              ( Focus.updateM
                  ( \(tr, p) ->
                      unsafeIOToSTM (deRefWeak p) >>= \case
                        Nothing -> return Nothing
                        Just _ -> return (Just (tr, p))
                  )
              )
              key
              (dbRefs db)
        return ptr
      SMap.insert (typeRep (Proxy @a), ptr) key (dbRefs db)
      v <- unsafeIOToSTM $ do
        mvar <- newEmptyMVar
        _ <- forkIO $ readForDB db key mvar
        takeMVar mvar
      writeTVar ref v
      return (DBRef db key ref)

readDBRef :: DBRef a -> STM (Maybe a)
readDBRef (DBRef _ _ ref) = do
  readTVar ref >>= \case
    Loading -> retry
    Missing -> return Nothing
    Present a -> return (Just a)

writeDBRef :: DBStorable a => DBRef a -> a -> STM ()
writeDBRef (DBRef db dbkey ref) a = do
  writeTVar ref (Present a)
  d <- readTVar (dbDirty db)
  writeTVar (dbDirty db) (Map.insert dbkey (SomeTVar ref, Just (putDB a)) d)

delDBRef :: DBStorable a => DBRef a -> STM ()
delDBRef (DBRef db dbkey ref) = do
  writeTVar ref Missing
  d <- readTVar (dbDirty db)
  writeTVar (dbDirty db) (Map.insert dbkey (SomeTVar ref, Nothing) d)