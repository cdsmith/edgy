{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Cardinality (Cardinality (..))
import Control.Concurrent.STM (STM)
import Control.Monad (filterM)
import Control.Monad.Extra (concatMapM)
import Data.Foldable (traverse_)
import Data.List ((\\))
import Data.Proxy (Proxy (..))
import Data.TCache (atomicallySync)
import Node
  ( Node,
    addRelated,
    bigBang,
    getAttribute,
    getRelated,
    newNode,
    setAttribute,
  )
import Schema
  ( Attribute (..),
    HasNode,
    NodeType (..),
    Relation (..),
    Schema,
    SchemaDef (..),
  )
import System.Environment (getArgs)
import GHC.TypeLits (Symbol)

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

type PersonNameAttr = NamedAttribute (DataNode "Person") "name" String

type PersonAgeAttr = NamedAttribute (DataNode "Person") "age" Int

type ActivityNameAttr = NamedAttribute (DataNode "Activity") "name" String

type ObjectNameAttr = NamedAttribute (DataNode "Object") "name" String

type SpouseRelation = Symmetric (DataNode "Person") One "spouse"

type FriendRelation = Directed (DataNode "Person") Many "friend" Many (DataNode "Person")

type HobbyRelation = Directed (DataNode "Person") Many "hobby" Many (DataNode "Activity")

type PossessionRelation = Directed (DataNode "Person") One "possession" Many (DataNode "Object")

type ToolRelation = Directed (DataNode "Activity") Many "tool" Many (DataNode "Object")

type MySchema :: Schema
type MySchema =
  '[ DefNode (DataNode "Person"),
     DefAttribute PersonNameAttr,
     DefAttribute PersonAgeAttr,
     DefRelation (Existence (DataNode "Person")),
     DefRelation SpouseRelation,
     DefRelation FriendRelation,
     DefNode (DataNode "Activity"),
     DefAttribute ActivityNameAttr,
     DefRelation (Existence (DataNode "Activity")),
     DefRelation HobbyRelation,
     DefNode (DataNode "Object"),
     DefAttribute ObjectNameAttr,
     DefRelation (Existence (DataNode "Object")),
     DefRelation PossessionRelation,
     DefRelation ToolRelation
   ]

instance IsNode MySchema Person where
  type NodeName MySchema Person = "Person"

  get node =
    Person
      <$> getAttribute (Proxy :: Proxy PersonNameAttr) node
      <*> getAttribute (Proxy :: Proxy PersonAgeAttr) node

  set node p = do
    setAttribute (Proxy :: Proxy PersonNameAttr) node (pName p)
    setAttribute (Proxy :: Proxy PersonAgeAttr) node (age p)

instance IsNode MySchema Activity where
  type NodeName MySchema Activity = "Activity"
  get node = Activity <$> getAttribute (Proxy :: Proxy ActivityNameAttr) node
  set node a = setAttribute (Proxy :: Proxy ActivityNameAttr) node (aName a)

instance IsNode MySchema Object where
  type NodeName MySchema Object = "Object"
  get node = Object <$> getAttribute (Proxy :: Proxy ObjectNameAttr) node
  set node o = setAttribute (Proxy :: Proxy ObjectNameAttr) node (oName o)

makeUniverse :: STM (Node MySchema Universe)
makeUniverse = do
  universe <- bigBang

  bob <- new Person {pName = "Bob", age = 20}
  jane <- new Person {pName = "Jane", age = 21}
  jose <- new Person {pName = "Jose", age = 22}

  addRelated (Proxy :: Proxy (Existence (DataNode "Person"))) universe bob
  addRelated (Proxy :: Proxy (Existence (DataNode "Person"))) universe jane
  addRelated (Proxy :: Proxy (Existence (DataNode "Person"))) universe jose

  poker <- new Activity {aName = "Poker"}
  hiking <- new Activity {aName = "Hiking"}

  addRelated (Proxy :: Proxy (Existence (DataNode "Activity"))) universe poker
  addRelated (Proxy :: Proxy (Existence (DataNode "Activity"))) universe hiking

  deckOfCards <- new Object {oName = "Deck of Cards"}
  pokerChips <- new Object {oName = "Poker Chips"}
  trekkingPoles <- new Object {oName = "Trekking Poles"}
  trailMap <- new Object {oName = "Trail Map"}

  addRelated (Proxy :: Proxy (Existence (DataNode "Object"))) universe deckOfCards
  addRelated (Proxy :: Proxy (Existence (DataNode "Object"))) universe pokerChips
  addRelated (Proxy :: Proxy (Existence (DataNode "Object"))) universe trekkingPoles
  addRelated (Proxy :: Proxy (Existence (DataNode "Object"))) universe trailMap

  addRelated (Proxy :: Proxy SpouseRelation) bob jane

  addRelated (Proxy :: Proxy FriendRelation) bob jane
  addRelated (Proxy :: Proxy FriendRelation) bob jose
  addRelated (Proxy :: Proxy FriendRelation) jose bob
  addRelated (Proxy :: Proxy FriendRelation) jane jose

  addRelated (Proxy :: Proxy HobbyRelation) bob poker
  addRelated (Proxy :: Proxy HobbyRelation) bob hiking
  addRelated (Proxy :: Proxy HobbyRelation) jane poker
  addRelated (Proxy :: Proxy HobbyRelation) jose hiking

  addRelated (Proxy :: Proxy PossessionRelation) bob trailMap
  addRelated (Proxy :: Proxy PossessionRelation) jane deckOfCards
  addRelated (Proxy :: Proxy PossessionRelation) jose trekkingPoles

  addRelated (Proxy :: Proxy ToolRelation) poker deckOfCards
  addRelated (Proxy :: Proxy ToolRelation) poker pokerChips
  addRelated (Proxy :: Proxy ToolRelation) hiking trekkingPoles
  addRelated (Proxy :: Proxy ToolRelation) hiking trailMap

  return universe

lookupPerson ::
  Node MySchema Universe ->
  String ->
  STM (Node MySchema (DataNode "Person"))
lookupPerson universe name = do
  people <- getRelated (Proxy :: Proxy (Existence (DataNode "Person"))) universe
  matches <- filterM (fmap ((== name) . pName) . get) people
  case matches of
    [person] -> return person
    [] -> error $ "No person named " ++ name
    _ -> error $ "Multiple people named " ++ name

missingTools ::
  Node MySchema (DataNode "Person") ->
  STM [Node MySchema (DataNode "Object")]
missingTools person = do
  todo <- getRelated (Proxy :: Proxy HobbyRelation) person
  needed <- concatMapM (getRelated (Proxy :: Proxy ToolRelation)) todo
  friends <- getRelated (Proxy :: Proxy FriendRelation) person
  available <-
    (++)
      <$> concatMapM
        (getRelated (Proxy :: Proxy PossessionRelation))
        friends
      <*> getRelated (Proxy :: Proxy PossessionRelation) person
  return (needed \\ available)

----------------------------------------

main :: IO ()
main =
  getArgs >>= \case
    ["create"] -> atomicallySync makeUniverse >> return ()
    ["query", name] -> do
      missingNames <- atomicallySync $ do
        universe <- bigBang
        bob <- lookupPerson universe name
        missing <- missingTools bob
        traverse (getAttribute (Proxy :: Proxy ObjectNameAttr)) missing
      putStrLn $ name ++ " is missing:"
      traverse_ putStrLn missingNames
    _ -> putStrLn "Usage: main [create|query]"
