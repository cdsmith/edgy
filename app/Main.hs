{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import Cardinality (Cardinality (..))
import Control.Concurrent.STM (STM, atomically)
import Control.Monad (filterM, (<=<))
import Control.Monad.Extra (concatMapM)
import Data.List ((\\))
import Data.Proxy (Proxy (..))
import Data.TCache (syncCache)
import Data.Typeable (Typeable)
import Schema
  ( Node,
    NodeType (..),
    Relation (..),
    SchemaDef (..),
    addRelated,
    bigBang,
    getAttr,
    getRelated,
    newNode,
    setAttr,
  )

class (Typeable schema, Typeable record) => IsNode schema record where
  get :: Node schema (DataNode record) -> STM record
  set :: Node schema (DataNode record) -> record -> STM ()

  new :: record -> STM (Node schema (DataNode record))
  new record = do
    node <- newNode
    set node record
    return node

data Person = Person {pName :: String, age :: Int} deriving (Show)

data Activity = Activity {aName :: String} deriving (Show)

data Object = Object {oName :: String} deriving (Show)

type MySchema =
  '[ AttrDef (DataNode Person) "pName" String,
     AttrDef (DataNode Person) "age" Int,
     AttrDef (DataNode Activity) "aName" String,
     AttrDef (DataNode Object) "oName" String,
     RelationDef (DataNode Person) One "spouse" (DataNode Person) One,
     RelationDef (DataNode Person) Many "friend" (DataNode Person) Many,
     RelationDef (DataNode Person) Many "hobby" (DataNode Activity) Many,
     RelationDef (DataNode Person) One "posession" (DataNode Object) Many,
     RelationDef (DataNode Activity) Many "tool" (DataNode Object) Many
   ]

personName :: Proxy "pName"
personName = Proxy

personAge :: Proxy "age"
personAge = Proxy

instance IsNode MySchema Person where
  get node = Person <$> getAttr personName node <*> getAttr personAge node

  set node p = do
    setAttr personName node (pName p)
    setAttr personAge node (age p)

activityName :: Proxy "aName"
activityName = Proxy

instance IsNode MySchema Activity where
  get node = Activity <$> getAttr activityName node
  set node a = setAttr activityName node (aName a)

objectName :: Proxy "oName"
objectName = Proxy

instance IsNode MySchema Object where
  get node = Object <$> getAttr objectName node
  set node o = setAttr objectName node (oName o)

existingPerson :: Proxy (Existence Person)
existingPerson = Proxy

existingActivity :: Proxy (Existence Activity)
existingActivity = Proxy

existingObject :: Proxy (Existence Object)
existingObject = Proxy

spouse :: Proxy (NamedRelation "spouse")
spouse = Proxy

friend :: Proxy (NamedRelation "friend")
friend = Proxy

hobby :: Proxy (NamedRelation "hobby")
hobby = Proxy

posession :: Proxy (NamedRelation "posession")
posession = Proxy

tool :: Proxy (NamedRelation "tool")
tool = Proxy

makeUniverse :: STM (Node MySchema Universe)
makeUniverse = do
  universe <- bigBang

  bob <- new Person {pName = "Bob", age = 20}
  jane <- new Person {pName = "Jane", age = 21}
  jose <- new Person {pName = "Jose", age = 22}

  addRelated existingPerson universe bob
  addRelated existingPerson universe jane
  addRelated existingPerson universe jose

  poker <- new Activity {aName = "Poker"}
  hiking <- new Activity {aName = "Hiking"}

  addRelated existingActivity universe poker
  addRelated existingActivity universe hiking

  deckOfCards <- new Object {oName = "Deck of Cards"}
  pokerChips <- new Object {oName = "Poker Chips"}
  trekkingPoles <- new Object {oName = "Trekking Poles"}
  trailMap <- new Object {oName = "Trail Map"}

  addRelated existingObject universe deckOfCards
  addRelated existingObject universe pokerChips
  addRelated existingObject universe trekkingPoles
  addRelated existingObject universe trailMap

  addRelated spouse bob jane

  addRelated friend bob jane
  addRelated friend bob jose

  addRelated hobby bob poker
  addRelated hobby bob hiking

  addRelated posession jane deckOfCards
  addRelated posession jose trekkingPoles

  addRelated tool poker deckOfCards
  addRelated tool poker pokerChips
  addRelated tool hiking trekkingPoles
  addRelated tool hiking trailMap

  return universe

----------------------------------------

main :: IO ()
main = do
  universe <- atomically makeUniverse
  toolNames <- atomically $ do
    -- We want to know the names of tools that are needed for Bob's hobbies,
    -- but are not owned by any of Bob's friends.
    bobs <- peopleByName universe "Bob"
    let bob = case bobs of
          [x] -> x
          _ -> error "Wrong number of bobs"
    todo <- getRelated hobby bob
    needed <- concatMapM (getRelated tool) todo
    friends <- getRelated friend bob
    available <- concatMapM (getRelated posession) friends
    let missing = needed \\ available
    mapM (getAttr objectName) missing
  putStrLn "Bob should buy:"
  mapM_ putStrLn toolNames
  syncCache

peopleByName ::
  Node MySchema Universe ->
  String ->
  STM [Node MySchema (DataNode Person)]
peopleByName universe name =
  filterM (return . (== name) . pName <=< get)
    =<< getRelated existingPerson universe
