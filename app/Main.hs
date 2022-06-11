{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Cardinality (Cardinality (..))
import Control.Concurrent.STM (STM)
import Control.Monad (filterM)
import Control.Monad.Extra (concatMapM)
import Data.Foldable (traverse_)
import Data.List ((\\))
import Data.TCache (atomicallySync)
import GHC.TypeLits (Symbol)
import Edgy
  ( Node,
    addRelated,
    bigBang,
    getAttribute,
    getRelated,
    newNode,
    setAttribute,
  )
import Schema
  ( AttributeSpec (..),
    HasNode,
    NodeType (..),
    RelationId (..),
    Schema,
    SchemaDef (..),
  )
import System.Environment (getArgs)

class HasNode schema (DataNode (NodeName schema record)) => IsNode schema record where
  type NodeName schema record :: Symbol

  get :: Node schema (DataNode (NodeName schema record)) -> STM record
  set :: Node schema (DataNode (NodeName schema record)) -> record -> STM ()

  new :: record -> STM (Node schema (DataNode (NodeName schema record)))
  new record = do
    node <- newNode
    set node record
    return node

data Person = Person
  { pName :: String,
    age :: Int
  }
  deriving (Show)

data Activity = Activity
  { aName :: String
  }
  deriving (Show)

data Object = Object
  { oName :: String
  }
  deriving (Show)

type MySchema :: Schema
type MySchema =
  '[ DefNode (DataNode "Person"),
     DefAttribute (Attribute (DataNode "Person") "name" String),
     DefAttribute (Attribute (DataNode "Person") "age" Int),
     DefSymmetric "spouse" (DataNode "Person") Optional,
     DefDirected "friend" (DataNode "Person") Many (DataNode "Person") Many,
     DefNode (DataNode "Activity"),
     DefAttribute (Attribute (DataNode "Activity") "name" String),
     DefDirected "hobby" (DataNode "Person") Many (DataNode "Activity") Many,
     DefNode (DataNode "Object"),
     DefAttribute (Attribute (DataNode "Object") "name" String),
     DefDirected "possession" (DataNode "Person") Many (DataNode "Object") Many,
     DefDirected "tool" (DataNode "Activity") Many (DataNode "Object") Many
   ]

instance IsNode MySchema Person where
  type NodeName MySchema Person = "Person"

  get node =
    Person
      <$> getAttribute @"name" node
      <*> getAttribute @"age" node

  set node p = do
    setAttribute @"name" node (pName p)
    setAttribute @"age" node (age p)

instance IsNode MySchema Activity where
  type NodeName MySchema Activity = "Activity"
  get node = Activity <$> getAttribute @"name" node
  set node a = setAttribute @"name" node (aName a)

instance IsNode MySchema Object where
  type NodeName MySchema Object = "Object"
  get node = Object <$> getAttribute @"name" node
  set node o = setAttribute @"name" node (oName o)

makeUniverse :: STM (Node MySchema Universe)
makeUniverse = do
  universe <- bigBang

  bob <- new Person {pName = "Bob", age = 20}
  jane <- new Person {pName = "Jane", age = 21}
  jose <- new Person {pName = "Jose", age = 22}

  addRelated @(Existence (DataNode "Person")) universe bob
  addRelated @(Existence (DataNode "Person")) universe jane
  addRelated @(Existence (DataNode "Person")) universe jose

  poker <- new Activity {aName = "Poker"}
  hiking <- new Activity {aName = "Hiking"}

  addRelated @(Existence (DataNode "Activity")) universe poker
  addRelated @(Existence (DataNode "Activity")) universe hiking

  deckOfCards <- new Object {oName = "Deck of Cards"}
  pokerChips <- new Object {oName = "Poker Chips"}
  trekkingPoles <- new Object {oName = "Trekking Poles"}
  trailMap <- new Object {oName = "Trail Map"}

  addRelated @(Existence (DataNode "Object")) universe deckOfCards
  addRelated @(Existence (DataNode "Object")) universe pokerChips
  addRelated @(Existence (DataNode "Object")) universe trekkingPoles
  addRelated @(Existence (DataNode "Object")) universe trailMap

  addRelated @(Explicit "spouse") bob jane

  addRelated @(Explicit "friend") bob jane
  addRelated @(Explicit "friend") bob jose
  addRelated @(Explicit "friend") jose bob
  addRelated @(Explicit "friend") jane jose

  addRelated @(Explicit "hobby") bob poker
  addRelated @(Explicit "hobby") bob hiking
  addRelated @(Explicit "hobby") jane poker
  addRelated @(Explicit "hobby") jose hiking

  addRelated @(Explicit "possession") bob trailMap
  addRelated @(Explicit "possession") jane deckOfCards
  addRelated @(Explicit "possession") jose trekkingPoles

  addRelated @(Explicit "tool") poker deckOfCards
  addRelated @(Explicit "tool") poker pokerChips
  addRelated @(Explicit "tool") hiking trekkingPoles
  addRelated @(Explicit "tool") hiking trailMap

  return universe

lookupPerson ::
  Node MySchema Universe ->
  String ->
  STM (Node MySchema (DataNode "Person"))
lookupPerson universe name = do
  people <- getRelated @(Existence (DataNode "Person")) universe
  matches <- filterM (fmap ((== name) . pName) . get) people
  case matches of
    [person] -> return person
    [] -> error $ "No person named " ++ name
    _ -> error $ "Multiple people named " ++ name

missingTools ::
  Node MySchema (DataNode "Person") ->
  STM [Node MySchema (DataNode "Object")]
missingTools person = do
  todo <- getRelated @(Explicit "hobby") person
  needed <- concatMapM (getRelated @(Explicit "tool")) todo
  friends <- getRelated @(Explicit "friend") person
  available <-
    (++)
      <$> concatMapM
        (getRelated @(Explicit "possession"))
        friends
      <*> getRelated @(Explicit "possession") person
  return (needed \\ available)

----------------------------------------

main :: IO ()
main =
  getArgs >>= \case
    ["create"] -> atomicallySync makeUniverse >> return ()
    ["query", name] -> do
      missingNames <- atomicallySync $ do
        universe <- bigBang
        person <- lookupPerson universe name
        missing <- missingTools person
        traverse (getAttribute @"name") missing
      putStrLn $ name ++ " is missing:"
      traverse_ putStrLn missingNames
    _ -> putStrLn "Usage: main [create|query]"
