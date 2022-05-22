{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Concurrent.STM (STM, TVar, newTVar)
import Control.Monad.ST (RealWorld)
import Data.Dependent.Map (DMap)
import Data.Functor.Compose (Compose)
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import Data.Unique.Tag (Tag, newTag)
import GHC.IO.Exception (IOErrorType (PermissionDenied))
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Dependent.Map as DMap

------ ACTUAL IMPL -------------

-- Schema API:

data RelTuple (a :: k) (b :: k)

data FieldTuple (a :: k) (b :: Type)

data Relation (a :: k) (b :: k) = Relation (Tag RealWorld (RelTuple a b)) deriving (Eq, Ord)

data Field (a :: k) (b :: Type) = Field {
    fieldTag :: Tag RealWorld (FieldTuple a b),
    fieldDefault :: b
    }

instance Eq (Field a b) where
    Field a _ == Field b _ = a == b

instance Ord (Field a b) where
    compare (Field a _) (Field b _) = compare a b

newRelation :: forall k (a :: k) (b :: k). IO (Relation a b)
newRelation = Relation <$> newTag

newField :: forall k (a :: k) (b :: Type). Monoid b => IO (Field a b)
newField = Field <$> newTag <*> pure mempty

newFieldWithDefault :: forall k (a :: k) (b :: Type). b -> IO (Field a b)
newFieldWithDefault def = Field <$> newTag <*> pure def

data Node (a :: k) = Node (TVar (NodeImpl a))

data NodeImpl (a :: k) = NodeImpl
  { fields :: DMap (Field a) Identity,
    relations :: DMap (Relation a) (Compose [] Node)
  }

-- Low-level API:

newNode :: STM (Node a)
newNode = do
    var <- newTVar (NodeImpl DMap.empty DMap.empty)
    return (Node var)

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

-- Efficient lookup: TBD - relations can be indexed by any ordered field

-- Query API: TBD

data Query (a :: k) (b :: Type) where
  QueryField :: Field a t -> Query a t
  QueryRelation :: Relation a b -> Filter b -> Query b t -> Query a [t]
  QueryComputed :: (b -> c) -> Query a b -> Query a c
  QueryConst :: t -> Query a t
  QueryApp :: Query a (b -> c) -> Query a b -> Query a c

type Filter b = Node b -> STM Bool

instance Functor (Query a) where
  fmap :: (b -> c) -> Query a b -> Query a c
  fmap = QueryComputed

instance Applicative (Query a) where
  pure :: t -> Query a t
  pure = QueryConst

  (<*>) :: Query a (b -> c) -> Query a b -> Query a c
  (<*>) = QueryApp

-- TBD: Monad instance?

query :: Node a -> Query a t -> STM t
query = undefined

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

nameLen :: Query Person Int
nameLen = QueryComputed length (QueryField personName)

----------------------------------------

main :: IO ()
main = return ()
