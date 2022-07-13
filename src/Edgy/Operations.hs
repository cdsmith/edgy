{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Edgy.Operations where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.Concurrent.STM (STM)
import Control.Monad (forM_)
import Control.Monad.STM.Class (MonadSTM (..))
import Data.Binary (Binary)
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Kind (Type)
import Data.List ((\\))
import Data.Type.Equality (testEquality, (:~:) (..))
import Data.Typeable (Proxy (..), Typeable)
import Data.UUID (UUID)
import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID
import Edgy.Cardinality (KnownCardinality (..), Numerous)
import Edgy.DB (DB, DBRef, delDBRef, getDBRef, readDBRef, writeDBRef)
import Edgy.Node
  ( AttributeKey (..),
    AttributeVal (..),
    Node (..),
    NodeImpl (..),
    Nodes (..),
    RelatedKey (..),
    RelatedVal (..),
    emptyNodeImpl,
    relatedKey,
  )
import Edgy.Schema
  ( AttributeSpec (..),
    AttributeType,
    Constructor,
    ExistenceSpec,
    HasAttribute,
    HasNode,
    HasRelation,
    KnownSchema,
    Mutability (..),
    NodeType (..),
    RelationName,
    RelationSpec (..),
    Schema,
    Target,
    TargetCardinality,
    UniversalSpec,
    attributeDefault,
    foldConstructor,
    foldRelations,
    mapConstructor,
  )
import GHC.Conc (unsafeIOToSTM)
import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)
import Type.Reflection (TypeRep, typeRep)

type Edgy :: Schema -> Type -> Type
newtype Edgy schema a = Edgy (DB -> STM a)
  deriving (Functor)

runEdgy :: DB -> Edgy schema a -> STM a
runEdgy db (Edgy f) = f db

instance Applicative (Edgy schema) where
  pure = Edgy . const . pure
  Edgy f <*> Edgy x = Edgy $ \db -> f db <*> x db

instance Monad (Edgy schema) where
  Edgy x >>= f = Edgy $ \db -> x db >>= \a -> runEdgy db (f a)

instance MonadSTM (Edgy schema) where
  liftSTM = Edgy . const

newNodeRef ::
  (KnownSchema schema, Typeable nodeType) =>
  DB ->
  STM (UUID, DBRef (NodeImpl schema nodeType))
newNodeRef db = do
  uuid <- unsafeIOToSTM $ do
    result <- newEmptyMVar
    _ <- forkIO $ UUID.nextRandom >>= putMVar result
    takeMVar result
  ref <- getDBRef db (show uuid)
  readDBRef ref >>= \case
    Nothing -> return (uuid, ref)
    _ -> newNodeRef db

getEdges ::
  forall (spec :: RelationSpec) {nodeType :: NodeType} {schema :: Schema}.
  ( KnownSchema schema,
    Typeable nodeType,
    Typeable spec,
    KnownSymbol (RelationName spec),
    Typeable (Target spec)
  ) =>
  DB ->
  Node schema nodeType ->
  STM [Node schema (Target spec)]
getEdges db (Node ref) =
  readDBRef ref >>= \case
    Just (NodeImpl uuid _ relations) -> do
      let result = DMap.lookup (RelatedKey (typeRep :: TypeRep spec)) relations
      nref <- case result of
        Just (RelatedVal r) -> pure r
        Nothing -> getDBRef db (relatedKey uuid (Proxy @spec))
      readDBRef nref >>= \case
        Just (Nodes _ ns) -> return ns
        Nothing -> return []
    Nothing -> error ("node not found: " ++ show ref)

modifyEdges ::
  forall (spec :: RelationSpec) {nodeType :: NodeType} {schema :: Schema}.
  ( KnownSchema schema,
    Typeable nodeType,
    Typeable spec,
    KnownSymbol (RelationName spec),
    Typeable (Target spec)
  ) =>
  DB ->
  Node schema nodeType ->
  ([Node schema (Target spec)] -> [Node schema (Target spec)]) ->
  STM ()
modifyEdges db (Node ref) f =
  readDBRef ref >>= \case
    Just (NodeImpl uuid attrs relations) -> do
      let rkey = RelatedKey (typeRep :: TypeRep spec)
      nref <- case DMap.lookup rkey relations of
        Just (RelatedVal nref) -> return nref
        Nothing -> do
          nref <- getDBRef db (relatedKey uuid (Proxy @spec))
          writeDBRef
            ref
            (NodeImpl uuid attrs (DMap.insert rkey (RelatedVal nref) relations))
          return nref
      readDBRef nref >>= \case
        Just (Nodes _ ns) -> writeDBRef nref (Nodes uuid (f ns))
        Nothing -> writeDBRef nref (Nodes uuid (f []))
    Nothing -> error ("node not found: " ++ show ref)

getUniverse :: KnownSchema schema => Edgy schema (Node schema Universe)
getUniverse = Edgy $ \db -> do
  ref <- getDBRef db (show UUID.nil)
  readDBRef ref >>= \case
    Nothing -> writeDBRef ref (emptyNodeImpl UUID.nil)
    _ -> return ()
  return (Node ref)

newNode ::
  forall (schema :: Schema) (typeName :: Symbol) {attrs :: [AttributeSpec]}.
  (KnownSymbol typeName, HasNode schema (DataNode typeName) attrs) =>
  Constructor attrs (Edgy schema (Node schema (DataNode typeName)))
newNode =
  mapConstructor (Proxy @(DataNode typeName)) (Proxy @attrs) mkNode $
    ( foldConstructor
        (Proxy @(DataNode typeName))
        (Proxy @attrs)
        setAttr
        DMap.empty
    )
  where
    setAttr ::
      forall (attr :: AttributeSpec).
      (Typeable attr, Binary (AttributeType attr)) =>
      Proxy attr ->
      AttributeType attr ->
      DMap (AttributeKey schema) (AttributeVal schema) ->
      DMap (AttributeKey schema) (AttributeVal schema)
    setAttr (_ :: Proxy attr) val attrs =
      DMap.insert (AttributeKey @attr @schema typeRep) (AttributeVal val) attrs

    mkNode attrs = Edgy @schema $ \db -> do
      (uuid, ref) <- newNodeRef db
      writeDBRef ref (NodeImpl uuid attrs DMap.empty)
      let node = Node ref
      universe <- Node <$> getDBRef db (show UUID.nil) :: STM (Node schema Universe)
      modifyEdges @(ExistenceSpec typeName) db universe (node :)
      modifyEdges @(UniversalSpec typeName) db node (const [universe])
      return node

deleteNode ::
  forall (typeName :: Symbol) {schema :: Schema} {attrs :: [AttributeSpec]}.
  (KnownSymbol typeName, HasNode schema (DataNode typeName) attrs) =>
  Node schema (DataNode typeName) ->
  Edgy schema ()
deleteNode node@(Node ref) = Edgy $ \db -> do
  foldRelations
    (Proxy @schema)
    (Proxy @(DataNode typeName))
    ( \(_ :: Proxy relation) (_ :: Proxy inverse) delRemaining -> do
        case testEquality
          (typeRep @(DataNode typeName))
          (typeRep @(Target inverse)) of
          Just Refl -> do
            nodes <- getEdges @relation db node
            forM_ nodes $ \n -> do
              modifyEdges @inverse db n (filter (/= node))
          _ -> return ()
        delRemaining
    )
    (return ())
  delDBRef ref

getAttribute ::
  forall
    (name :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {attr :: AttributeSpec}.
  HasAttribute schema nodeType name attr =>
  Node schema nodeType ->
  Edgy schema (AttributeType attr)
getAttribute (Node ref) = Edgy $ \_db -> do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl _ attrs _) ->
      case DMap.lookup (AttributeKey (typeRep :: TypeRep attr)) attrs of
        Just (AttributeVal val) -> return val
        Nothing -> case attributeDefault (Proxy @schema) (Proxy @nodeType) (Proxy @name) of
          Just def -> return def
          Nothing ->
            error
              ( "getAttribute: Required attribute not defined: "
                  ++ symbolVal (Proxy @name)
                  ++ " on "
                  ++ show ref
              )
    Nothing -> error ("getAttribute: node not found: " ++ show ref)

setAttribute ::
  forall
    (name :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {attr :: AttributeSpec}.
  HasAttribute schema nodeType name attr =>
  Node schema nodeType ->
  AttributeType attr ->
  Edgy schema ()
setAttribute (Node ref) value = Edgy $ \_db -> do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) ->
      writeDBRef
        ref
        ( NodeImpl
            uuid
            ( DMap.insert
                (AttributeKey (typeRep :: TypeRep attr))
                (AttributeVal value)
                attrs
            )
            relations
        )
    Nothing -> error ("setAttribute: node not found: " ++ show ref)

getRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}
    {mutability :: Mutability}.
  HasRelation schema nodeType relation spec inverse mutability =>
  Node schema nodeType ->
  Edgy schema (Numerous (TargetCardinality spec) (Node schema (Target spec)))
getRelated node = Edgy $ \db -> do
  listToNumerous @(TargetCardinality spec) <$> getEdges @spec db node >>= \case
    Just result -> return result
    Nothing -> error "getRelated: bad cardinality"

isRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}
    {mutability :: Mutability}.
  HasRelation schema nodeType relation spec inverse mutability =>
  Node schema nodeType ->
  Node schema (Target spec) ->
  Edgy schema Bool
isRelated node target = Edgy $ \db -> elem target <$> getEdges @spec db node

setRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema nodeType relation spec inverse Mutable =>
  Node schema nodeType ->
  Numerous (TargetCardinality spec) (Node schema (Target spec)) ->
  Edgy schema ()
setRelated a target = Edgy $ \db -> do
  oldNodes <- getEdges @spec db a
  let newNodes = numerousToList @(TargetCardinality spec) target
  modifyEdges @spec db a (const newNodes)
  forM_ (oldNodes \\ newNodes) $ \b -> modifyEdges @inverse db b (filter (/= a))
  forM_ (newNodes \\ oldNodes) $ \b -> modifyEdges @inverse db b (a :)

addRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema nodeType relation spec inverse Mutable =>
  Node schema nodeType ->
  Node schema (Target spec) ->
  Edgy schema ()
addRelated a b = Edgy $ \db -> do
  modifyEdges @spec db a (b :)
  modifyEdges @inverse db b (a :)

removeRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema nodeType relation spec inverse Mutable =>
  Node schema nodeType ->
  Node schema (Target spec) ->
  Edgy schema ()
removeRelated a b = Edgy $ \db -> do
  modifyEdges @spec db a (filter (/= b))
  modifyEdges @inverse db b (filter (/= a))

clearRelated ::
  forall
    (relation :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema nodeType relation spec inverse Mutable =>
  Node schema nodeType ->
  Edgy schema ()
clearRelated node = Edgy $ \db -> do
  nodes <- getEdges @spec db node
  forM_ nodes $ \n -> do
    modifyEdges @inverse db n (filter (/= node))
  modifyEdges @spec db node (const [])
