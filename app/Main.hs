{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Monad.ST (RealWorld)
import Data.Unique.Tag (Tag, newTag)
import GHC.IO.Exception (IOErrorType (PermissionDenied))
import System.IO.Unsafe (unsafePerformIO)
import Data.Kind (Type)
import Control.Concurrent.STM (STM)

------ ACTUAL IMPL -------------

-- Schema API:

data RelTuple (a :: k) (b :: k)
data FieldTuple (a :: k) (b :: Type)

data Relation (a :: k) (b :: k) = Relation (Tag RealWorld (RelTuple a b)) deriving (Eq, Ord)

data Field (a :: k) (b :: Type) = Field (Tag RealWorld (FieldTuple a b)) deriving (Eq, Ord)

newRelation :: forall k (a :: k) (b :: k). IO (Relation a b)
newRelation = Relation <$> newTag

newField :: forall k (a :: k) (b :: Type). IO (Field a b)
newField = Field <$> newTag

data Node (a :: k)

-- Low-level API:

newNode :: STM (Node a)
newNode = undefined

setField :: Node a -> Field a t -> t -> STM ()
setField = undefined

getField :: Node a -> Field a t -> STM t
getField = undefined

addToRelation :: Node a -> Relation a b -> Node b -> STM ()
addToRelation = undefined

removeFromRelation :: Node a -> Relation a b -> Node b -> STM ()
removeFromRelation = undefined

getRelated :: Node a -> Relation a b -> STM [Node b]
getRelated = undefined

-- Query API: TBD

------ EXAMPLE -----------------

data Person

data Activity

personName :: Field Person String
personName = unsafePerformIO newField

activityName :: Field Activity String
activityName = unsafePerformIO newField

friend :: Relation Person Person
friend = unsafePerformIO newRelation

hobby :: Relation Person Person
hobby = unsafePerformIO newRelation

----------------------------------------

main :: IO ()
main = return ()
