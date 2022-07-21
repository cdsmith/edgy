{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Concurrent.STM (atomically)
import Control.Monad (filterM)
import Control.Monad.Extra (concatMapM)
import Data.Foldable (traverse_)
import Data.List ((\\))
import Data.Proxy (Proxy (..))
import Edgy
  ( AttributeSpec (..),
    Cardinality (..),
    Edgy,
    HasAttribute,
    HasRelation,
    Mutability,
    Node,
    NodeType (..),
    RelationSpec (..),
    Schema,
    SchemaDef (..),
    SchemaValidator (..),
    Target,
    TargetCardinality,
    addRelated,
    getAttribute,
    getRelated,
    getUniverse,
    newNode,
    removeRelated,
    runEdgy,
  )
import GHC.TypeLits (Symbol, symbolVal)
import PersistentSTM (filePersistence, withDB)
import System.Environment (getArgs)

type MySchema =
  '[ DefNode
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
        ],
     DefSymmetric
       (Relation "spouse" Optional (DataNode "Person")),
     DefDirected
       (Relation "friend" Many (DataNode "Person"))
       (Relation "friendOf" Many (DataNode "Person")),
     DefDirected
       (Relation "hobby" Many (DataNode "Activity"))
       (Relation "enthusiast" Many (DataNode "Person")),
     DefDirected
       (Relation "possession" Many (DataNode "Object"))
       (Relation "owner" Many (DataNode "Person")),
     DefDirected
       (Relation "tool" Many (DataNode "Object"))
       (Relation "application" Many (DataNode "Activity"))
   ]

_ = ValidateSchema @MySchema

bigBang :: Edgy MySchema (Node MySchema Universe)
bigBang = do
  universe <- getUniverse

  bob <- newNode @MySchema @"Person" "Bob" 20
  jane <- newNode @MySchema @"Person" "Jane" 21
  jose <- newNode @MySchema @"Person" "Jose" 22

  poker <- newNode @MySchema @"Activity" "Poker"
  hiking <- newNode @MySchema @"Activity" "Hiking"

  deckOfCards <- newNode @MySchema @"Object" "Deck of Cards"
  pokerChips <- newNode @MySchema @"Object" "Poker Chips"
  trekkingPoles <- newNode @MySchema @"Object" "Trekking Poles"
  trailMap <- newNode @MySchema @"Object" "Trail Map"

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

lookupByName ::
  forall
    (typeName :: Symbol)
    (schema :: Schema)
    (spec :: RelationSpec)
    (inverse :: RelationSpec)
    (mutability :: Mutability).
  ( HasRelation schema Universe typeName spec inverse mutability,
    HasAttribute schema (DataNode typeName) "name" ("name" ::: String),
    Target spec ~ DataNode typeName,
    TargetCardinality spec ~ Many
  ) =>
  String ->
  Edgy schema (Node schema (DataNode typeName))
lookupByName name = do
  universe <- getUniverse
  nodes <-
    getRelated @typeName universe
      >>= filterM (fmap (== name) . getAttribute @"name")
  case nodes of
    [node] -> return node
    [] -> error $ "No " ++ symbolVal (Proxy @typeName) ++ " named " ++ name
    _ -> error $ "Multiple " ++ symbolVal (Proxy @typeName) ++ " named " ++ name

lookupPerson :: String -> Edgy MySchema (Node MySchema (DataNode "Person"))
lookupPerson = lookupByName

lookupObject :: String -> Edgy MySchema (Node MySchema (DataNode "Object"))
lookupObject = lookupByName

missingTools ::
  Node MySchema (DataNode "Person") ->
  Edgy MySchema [Node MySchema (DataNode "Object")]
missingTools person = do
  needed <- concatMapM (getRelated @"tool") =<< getRelated @"hobby" person
  available <-
    (++)
      <$> (concatMapM (getRelated @"possession") =<< getRelated @"friend" person)
      <*> getRelated @"possession" person
  return (needed \\ available)

----------------------------------------

main :: IO ()
main = do
  persister <- filePersistence ".db"
  withDB persister $ \db -> do
    getArgs >>= \case
      ["create"] -> atomically (runEdgy db bigBang) >> return ()
      ["query", name] -> do
        missingNames <- atomically $
          runEdgy db $ do
            person <- lookupPerson name
            missing <- missingTools person
            traverse (getAttribute @"name") missing
        putStrLn $ name ++ " is missing:"
        traverse_ putStrLn missingNames
      ["buy", name, tool] -> atomically $
        runEdgy db $ do
          person <- lookupPerson name
          object <- lookupObject tool
          addRelated @"possession" person object
      ["discard", name, tool] -> atomically $
        runEdgy db $ do
          person <- lookupPerson name
          object <- lookupObject tool
          removeRelated @"possession" person object
      ["friend", name1, name2] -> atomically $
        runEdgy db $ do
          person1 <- lookupPerson name1
          person2 <- lookupPerson name2
          addRelated @"friend" person1 person2
      ["unfriend", name1, name2] -> atomically $
        runEdgy db $ do
          person1 <- lookupPerson name1
          person2 <- lookupPerson name2
          removeRelated @"friend" person1 person2
      ["marry", name1, name2] -> atomically $
        runEdgy db $ do
          person1 <- lookupPerson name1
          person2 <- lookupPerson name2
          addRelated @"spouse" person1 person2
      ["divorce", name1, name2] -> atomically $
        runEdgy db $ do
          person1 <- lookupPerson name1
          person2 <- lookupPerson name2
          removeRelated @"spouse" person1 person2
      _ -> putStrLn "Usage: main [cmd]"
