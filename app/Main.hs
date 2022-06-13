{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Control.Monad (filterM)
import Control.Monad.Extra (concatMapM)
import Data.Foldable (traverse_)
import Data.List ((\\))
import Data.TCache (atomicallySync)
import Edgy
  ( AttributeSpec (..),
    Cardinality (..),
    Edgy (..),
    HasAttribute,
    HasNode,
    IsNode (..),
    Node,
    NodeType (..),
    SchemaDef (..),
    addRelated,
    getAttribute,
    getRelated,
    getUniverse,
    removeRelated,
    setAttribute,
  )
import System.Environment (getArgs)

data Person = Person
  { pName :: String,
    age :: Int
  }
  deriving (Show)

instance
  ( HasNode schema (DataNode "Person"),
    HasAttribute schema (DataNode "Person") "name" ("name" ::: String),
    HasAttribute schema (DataNode "Person") "age" ("age" ::: Int)
  ) =>
  IsNode schema Person
  where
  type NodeName schema Person = "Person"

  get node =
    Person
      <$> getAttribute @"name" node
      <*> getAttribute @"age" node

  set node p = do
    setAttribute @"name" node (pName p)
    setAttribute @"age" node (age p)

data Activity = Activity
  { aName :: String
  }
  deriving (Show)

instance
  ( HasNode schema (DataNode "Activity"),
    HasAttribute schema (DataNode "Activity") "name" ("name" ::: String)
  ) =>
  IsNode schema Activity
  where
  type NodeName schema Activity = "Activity"
  get node = Activity <$> getAttribute @"name" node
  set node a = setAttribute @"name" node (aName a)

data Object = Object
  { oName :: String
  }
  deriving (Show)

instance
  ( HasNode schema (DataNode "Object"),
    HasAttribute schema (DataNode "Object") "name" ("name" ::: String)
  ) =>
  IsNode schema Object
  where
  type NodeName schema Object = "Object"
  get node = Object <$> getAttribute @"name" node
  set node o = setAttribute @"name" node (oName o)

type MySchema =
  '[ DefSymmetric "spouse" Optional (DataNode "Person"),
     DefDirected "friend" Many (DataNode "Person") "friendOf" Many (DataNode "Person"),
     DefDirected "hobby" Many (DataNode "Activity") "enthusiast" Many (DataNode "Person"),
     DefDirected "possession" Many (DataNode "Object") "owner" Many (DataNode "Person"),
     DefDirected "tool" Many (DataNode "Object") "application" Many (DataNode "Activity"),
     DefNode
       (DataNode "Person")
       '[ "name" ::: String,
          "age" ::: Int
        ],
     DefNode
       (DataNode "Activity")
       '[ "name" ::: String
        ],
     DefNode
       (DataNode "Object")
       '[ "name" ::: String
        ]
   ]

bigBang :: Edgy MySchema (Node MySchema Universe)
bigBang = do
  universe <- getUniverse

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
  people <- getRelated @"Person" universe
  matches <- filterM (fmap ((== name) . pName) . get) people
  case matches of
    [person] -> return person
    [] -> error $ "No person named " ++ name
    _ -> error $ "Multiple people named " ++ name

lookupObject ::
  Node MySchema Universe ->
  String ->
  Edgy MySchema (Node MySchema (DataNode "Object"))
lookupObject universe name = do
  objs <- getRelated @"Object" universe
  matches <- filterM (fmap ((== name) . oName) . get) objs
  case matches of
    [obj] -> return obj
    [] -> error $ "No object named " ++ name
    _ -> error $ "Multiple objects named " ++ name

missingTools ::
  Node MySchema (DataNode "Person") ->
  Edgy MySchema [Node MySchema (DataNode "Object")]
missingTools person = do
  todo <- getRelated @"hobby" person
  needed <- concatMapM (getRelated @"tool") todo
  friends <- getRelated @"friend" person
  available <-
    (++)
      <$> concatMapM
        (getRelated @"possession")
        friends
      <*> getRelated @"possession" person
  return (needed \\ available)

----------------------------------------

main :: IO ()
main =
  getArgs >>= \case
    ["create"] -> atomicallySync (runEdgy bigBang) >> return ()
    ["query", name] -> do
      missingNames <- atomicallySync $
        runEdgy $ do
          universe <- getUniverse
          person <- lookupPerson universe name
          missing <- missingTools person
          traverse (getAttribute @"name") missing
      putStrLn $ name ++ " is missing:"
      traverse_ putStrLn missingNames
    ["buy", name, tool] -> atomicallySync $
      runEdgy $ do
        universe <- getUniverse
        person <- lookupPerson universe name
        object <- lookupObject universe tool
        addRelated @"possession" person object
    ["discard", name, tool] -> atomicallySync $
      runEdgy $ do
        universe <- getUniverse
        person <- lookupPerson universe name
        object <- lookupObject universe tool
        removeRelated @"possession" person object
    ["friend", name1, name2] -> atomicallySync $
      runEdgy $ do
        universe <- getUniverse
        person1 <- lookupPerson universe name1
        person2 <- lookupPerson universe name2
        addRelated @"friend" person1 person2
    ["unfriend", name1, name2] -> atomicallySync $
      runEdgy $ do
        universe <- getUniverse
        person1 <- lookupPerson universe name1
        person2 <- lookupPerson universe name2
        removeRelated @"friend" person1 person2
    ["marry", name1, name2] -> atomicallySync $
      runEdgy $ do
        universe <- getUniverse
        person1 <- lookupPerson universe name1
        person2 <- lookupPerson universe name2
        addRelated @"spouse" person1 person2
    ["divorce", name1, name2] -> atomicallySync $
      runEdgy $ do
        universe <- getUniverse
        person1 <- lookupPerson universe name1
        person2 <- lookupPerson universe name2
        removeRelated @"spouse" person1 person2
    _ -> putStrLn "Usage: main [cmd]"
