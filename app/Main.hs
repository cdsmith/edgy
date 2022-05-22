{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Concurrent.STM (STM, TVar, modifyTVar, newTVar, readTVar, atomically)
import Control.Monad (filterM, (<=<))
import Control.Monad.ST (RealWorld)
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Functor.Compose (Compose (..))
import Data.Functor.Identity (Identity (..))
import Data.GADT.Compare (GCompare (gcompare), GEq (geq), GOrdering (..))
import Data.Kind (Type)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Set.Extra as Set
import Data.Type.Equality (type (:~:) (Refl))
import Data.Unique (Unique, newUnique)
import Data.Unique.Tag (Tag, newTag)
import GHC.Conc (unsafeIOToSTM)
import System.IO.Unsafe (unsafePerformIO)

------ ACTUAL IMPL -------------

-- Schema API:

data RelTag (a :: k) (b :: k)

data FieldTag (a :: k) (b :: Type)

newtype Relation (a :: k) (b :: k) = Relation (Tag RealWorld (RelTag a b))
  deriving (Eq, Ord)

instance GEq (Relation a) where
  geq (Relation a) (Relation b) =
    case geq a b of
      Just Refl -> Just Refl
      Nothing -> Nothing

instance GCompare (Relation a) where
  gcompare (Relation a) (Relation b) =
    case gcompare a b of
      GLT -> GLT
      GEQ -> GEQ
      GGT -> GGT

newtype FieldRef (a :: k) (b :: Type) = FieldRef (Tag RealWorld (FieldTag a b))
  deriving (Eq, Ord)

instance GEq (FieldRef a) where
  geq (FieldRef a) (FieldRef b) = case geq a b of
    Just Refl -> Just Refl
    Nothing -> Nothing

instance GCompare (FieldRef a) where
  gcompare (FieldRef a) (FieldRef b) = case gcompare a b of
    GLT -> GLT
    GEQ -> GEQ
    GGT -> GGT

data Field (a :: k) (b :: Type) = Field
  { fieldTag :: FieldRef a b,
    fieldDefault :: b
  }

instance Eq (Field a b) where
  Field a _ == Field b _ = a == b

instance Ord (Field a b) where
  compare (Field a _) (Field b _) = compare a b

newRelation :: forall k (a :: k) (b :: k). IO (Relation a b)
newRelation = Relation <$> newTag

newField :: forall k (a :: k) (b :: Type). Monoid b => IO (Field a b)
newField = Field <$> (FieldRef <$> newTag) <*> pure mempty

newFieldWithDefault :: forall k (a :: k) (b :: Type). b -> IO (Field a b)
newFieldWithDefault def = Field <$> (FieldRef <$> newTag) <*> pure def

data Node (a :: k) = Node
  { nodeKey :: Unique,
    nodevar :: TVar (NodeImpl a)
  }

instance Eq (Node a) where
  Node a _ == Node b _ = a == b

instance Ord (Node a) where
  compare (Node a _) (Node b _) = compare a b

data NodeImpl (a :: k) = NodeImpl
  { nodeFields :: DMap (FieldRef a) Identity,
    nodeRelations :: DMap (Relation a) (Compose Set Node)
  }

-- Low-level API:

newNode :: STM (Node a)
newNode = do
  key <- unsafeIOToSTM newUnique
  var <- newTVar (NodeImpl DMap.empty DMap.empty)
  return (Node key var)

setField :: Field a t -> Node a -> t -> STM ()
setField (Field ref _) (Node _ var) val = modifyTVar var $
  \(NodeImpl fields rels) ->
    NodeImpl (DMap.insert ref (Identity val) fields) rels

getField :: Field a t -> Node a -> STM t
getField (Field ref def) (Node _ var) =
  readTVar var
    >>= \(NodeImpl fields _) ->
      case DMap.lookup ref fields of
        Just (Identity val) -> return val
        Nothing -> return def

addToRelation :: Relation a b -> Node a -> Node b -> STM ()
addToRelation rel (Node _ var) target = modifyTVar var $
  \(NodeImpl fields rels) ->
    NodeImpl
      fields
      (DMap.insertWith (<>) rel (Compose (Set.singleton target)) rels)

removeFromRelation :: Relation a b -> Node a -> Node b -> STM ()
removeFromRelation rel (Node _ var) target = modifyTVar var $
  \(NodeImpl fields rels) ->
    NodeImpl
      fields
      (DMap.adjust (Compose . Set.delete target . getCompose) rel rels)

getRelated :: Relation a b -> Node a -> STM (Set (Node b))
getRelated rel (Node _ var) =
  readTVar var >>= \(NodeImpl _ relMap) ->
    case DMap.lookup rel relMap of
      Just (Compose rels) -> return rels
      Nothing -> return mempty

-- Efficient lookup: TBD - relations can be indexed by any ordered field

-- Query API: TBD

data Query (a :: k) (b :: Type) where
  QuerySelf :: Query a (Node a)
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

query :: Query a t -> Node a -> STM t
query QuerySelf node = return node
query (QueryConst v) _node = return v
query (QueryComputed f q) node = fmap f (query q node)
query (QueryField field) node = getField field node
query (QueryRelation rel p q) node = do
  related <- filterM p . Set.toList =<< getRelated rel node
  traverse (query q) related
query (QueryApp q1 q2) node = query q1 node <*> query q2 node

------ ADT ADAPTOR -------------

class IsNode record where
  get :: Node record -> STM record
  set :: Node record -> record -> STM ()

  new :: record -> STM (Node record)
  new record = do
    node <- newNode
    set node record
    return node

------ EXAMPLE -----------------

data Universe

data Person = Person {pName :: String, age :: Int} deriving Show

personName :: Field Person String
personName = unsafePerformIO newField
{-# NOINLINE personName #-}

personAge :: Field Person Int
personAge = unsafePerformIO (newFieldWithDefault 18)
{-# NOINLINE personAge #-}

instance IsNode Person where
  get node = Person <$> getField personName node <*> getField personAge node

  set node p = do
    setField personName node (pName p)
    setField personAge node (age p)

data Activity = Activity {aName :: String} deriving Show

activityName :: Field Activity String
activityName = unsafePerformIO newField
{-# NOINLINE activityName #-}

instance IsNode Activity where
  get node = Activity <$> getField activityName node
  set node a = setField activityName node (aName a)

data Object = Object {oName :: String} deriving Show

objectName :: Field Object String
objectName = unsafePerformIO newField
{-# NOINLINE objectName #-}

instance IsNode Object where
    get node = Object <$> getField objectName node
    set node o = setField objectName node (oName o)

existingPerson :: Relation Universe Person
existingPerson = unsafePerformIO newRelation
{-# NOINLINE existingPerson #-}

existingActivity :: Relation Universe Activity
existingActivity = unsafePerformIO newRelation
{-# NOINLINE existingActivity #-}

existingObject :: Relation Universe Object
existingObject = unsafePerformIO newRelation
{-# NOINLINE existingObject #-}

spouse :: Relation Person Person
spouse = unsafePerformIO newRelation
{-# NOINLINE spouse #-}

friend :: Relation Person Person
friend = unsafePerformIO newRelation
{-# NOINLINE friend #-}

hobby :: Relation Person Activity
hobby = unsafePerformIO newRelation
{-# NOINLINE hobby #-}

posession :: Relation Person Object
posession = unsafePerformIO newRelation
{-# NOINLINE posession #-}

tool :: Relation Activity Object
tool = unsafePerformIO newRelation
{-# NOINLINE tool #-}

nameLen :: Query Person Int
nameLen = QueryComputed length (QueryField personName)

----------------------------------------

main :: IO ()
main = do
    universe <- atomically makeUniverse
    toolNames <- atomically $ do
        -- We want to know the names of tools that are needed for Bob's hobbies,
        -- but are not owned by any of Bob's friends.
        matchingBobs <- peopleByName universe "Bob"
        let [bob] = Set.toList matchingBobs
        todo <- getRelated hobby bob
        needed <- Set.concatMapM (getRelated tool) todo
        friends <- getRelated friend bob
        available <- Set.concatMapM (getRelated posession) friends
        let missing = Set.difference needed available
        mapM (getField objectName) (Set.toList missing)
    putStrLn "Bob should buy:"
    mapM_ putStrLn toolNames

peopleByName :: Node Universe -> String -> STM (Set (Node Person))
peopleByName universe name =
    Set.filterM (return . (== name) . pName <=< get)
        =<< getRelated existingPerson universe

makeUniverse :: STM (Node Universe)
makeUniverse = do
    universe <- newNode

    bob <- new Person {pName = "Bob", age = 20}
    jane <- new Person {pName = "Jane", age = 21}
    jose <- new Person {pName = "Jose", age = 22}

    addToRelation existingPerson universe bob
    addToRelation existingPerson universe jane
    addToRelation existingPerson universe jose

    poker <- new Activity { aName = "Poker" }
    hiking <- new Activity { aName = "Hiking" }

    addToRelation existingActivity universe poker
    addToRelation existingActivity universe hiking

    deckOfCards <- new Object { oName = "Deck of Cards" }
    pokerChips <- new Object { oName = "Poker Chips" }
    trekkingPoles <- new Object { oName = "Trekking Poles" }
    trailMap <- new Object { oName = "Trail Map" }

    addToRelation existingObject universe deckOfCards
    addToRelation existingObject universe pokerChips
    addToRelation existingObject universe trekkingPoles
    addToRelation existingObject universe trailMap

    addToRelation friend bob jane
    addToRelation friend bob jose

    addToRelation hobby bob poker
    addToRelation hobby bob hiking

    addToRelation posession jane deckOfCards
    addToRelation posession jose trekkingPoles

    addToRelation tool poker deckOfCards
    addToRelation tool poker pokerChips
    addToRelation tool hiking trekkingPoles
    addToRelation tool hiking trailMap

    return universe
