{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import Cardinality (Cardinality (..))
import Control.Monad (filterM)
import Control.Monad.Extra (concatMapM)
import Data.Foldable (traverse_)
import Data.List ((\\))
import Data.TCache (atomicallySync)
import Edgy
  ( Node,
    addRelated,
    bigBang,
    getAttribute,
    getRelated,
    newNode,
    setAttribute, Edgy, runEdgy
  )
import GHC.TypeLits (KnownSymbol, Symbol)
import Schema
  ( AttributeSpec (..),
    HasNode,
    NodeType (..),
    RelationId (..),
    Schema,
    SchemaDef (..),
  )
import System.Environment (getArgs)

class
  HasNode schema (DataNode (NodeName schema record)) =>
  IsNode schema record
  where
  type NodeName schema record :: Symbol

  get ::
    Node schema (DataNode (NodeName schema record)) ->
    Edgy schema record
  set ::
    Node schema (DataNode (NodeName schema record)) ->
    record ->
    Edgy schema ()

  new ::
    KnownSymbol (NodeName schema record) =>
    record ->
    Edgy schema (Node schema (DataNode (NodeName schema record)))
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
  '[ DefNode
       (DataNode "Person")
       '[ Attribute "name" String,
          Attribute "age" Int
        ],
     DefSymmetric (DataNode "Person") "spouse" Optional,
     DefDirected Many (DataNode "Person") "friend" Many (DataNode "Person"),
     DefNode
       (DataNode "Activity")
       '[ Attribute "name" String
        ],
     DefDirected Many (DataNode "Person") "hobby" Many (DataNode "Activity"),
     DefNode
       (DataNode "Object")
       '[ Attribute "name" String
        ],
     DefDirected Many (DataNode "Person") "possession" Many (DataNode "Object"),
     DefDirected Many (DataNode "Activity") "tool" Many (DataNode "Object")
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

makeUniverse :: Edgy MySchema (Node MySchema Universe)
makeUniverse = do
  universe <- bigBang

  bob <- new Person {pName = "Bob", age = 20}
  jane <- new Person {pName = "Jane", age = 21}
  jose <- new Person {pName = "Jose", age = 22}

  poker <- new Activity {aName = "Poker"}
  hiking <- new Activity {aName = "Hiking"}

  deckOfCards <- new Object {oName = "Deck of Cards"}
  pokerChips <- new Object {oName = "Poker Chips"}
  trekkingPoles <- new Object {oName = "Trekking Poles"}
  trailMap <- new Object {oName = "Trail Map"}

  addRelated @"spouse" bob jane

  addRelated @"friend" bob jane
  addRelated @"friend" bob jose
  addRelated @"friend" jose bob
  addRelated @"friend" jane jose

  addRelated @"hobby" bob poker
  addRelated @"hobby" bob hiking
  addRelated @"hobby" jane poker
  addRelated @"hobby" jose hiking

  addRelated @"possession" bob trailMap
  addRelated @"possession" jane deckOfCards
  addRelated @"possession" jose trekkingPoles

  addRelated @"tool" poker deckOfCards
  addRelated @"tool" poker pokerChips
  addRelated @"tool" hiking trekkingPoles
  addRelated @"tool" hiking trailMap

  return universe

lookupPerson ::
  Node MySchema Universe ->
  String ->
  Edgy MySchema (Node MySchema (DataNode "Person"))
lookupPerson universe name = do
  people <- getRelated @(Existence "Person") universe
  matches <- filterM (fmap ((== name) . pName) . get) people
  case matches of
    [person] -> return person
    [] -> error $ "No person named " ++ name
    _ -> error $ "Multiple people named " ++ name

missingTools ::
  Node MySchema (DataNode "Person") ->
  Edgy MySchema [Node MySchema (DataNode "Object")]
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
    ["create"] -> atomicallySync (runEdgy makeUniverse) >> return ()
    ["query", name] -> do
      missingNames <- atomicallySync $ runEdgy $ do
        universe <- bigBang
        person <- lookupPerson universe name
        missing <- missingTools person
        traverse (getAttribute @"name") missing
      putStrLn $ name ++ " is missing:"
      traverse_ putStrLn missingNames
    _ -> putStrLn "Usage: main [create|query]"
