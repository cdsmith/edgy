{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Edgy
  ( -- * The Edgy monad
    Edgy,
    runEdgy,
    liftSTM,

    -- * Nodes and operations
    Node,
    bigBang,
    newNode,
    deleteNode,
    getAttribute,
    setAttribute,
    getRelated,
    isRelated,
    setRelated,
    addRelated,
    removeRelated,
    clearRelated,

    -- * Schema types
    NodeType (..),
    RelationId (..),
    Schema,
    SchemaDef (..),
    Cardinality (..),
    AttributeSpec (..),
    HasNode,
  )
where

import Control.Monad (forM_)
import qualified Data.Dependent.Map as DMap
import Data.Kind (Type)
import Data.List ((\\))
import Data.TCache
  ( STM,
    delDBRef,
    getDBRef,
    newDBRef,
    readDBRef,
    safeIOToSTM,
    writeDBRef,
  )
import Data.Type.Equality (TestEquality (testEquality), (:~:) (..))
import Data.Typeable (Proxy (..), Typeable)
import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID
import Edgy.Cardinality (Cardinality (..), KnownCardinality (..), Numerous)
import Edgy.Node
  ( AttributeKey (..),
    AttributeVal (..),
    Node (..),
    NodeImpl (..),
    RelatedKey (..),
    RelatedVal (..),
    emptyNodeImpl,
  )
import Edgy.Schema
  ( AttributeSpec (..),
    AttributeType,
    Codomain,
    CodomainCardinality,
    Domain,
    ExistenceSpec,
    HasAttribute,
    HasNode,
    HasRelation,
    KnownSchema,
    NodeType (..),
    RelationId (..),
    RelationSpec (..),
    Schema,
    SchemaDef (..),
    UniversalSpec,
    foldRelations,
  )
import GHC.TypeLits (KnownSymbol, Symbol)
import Type.Reflection (TypeRep, typeRep)

type Edgy :: Schema -> Type -> Type
newtype Edgy schema a = Edgy {runEdgy :: STM a}
  deriving (Functor, Applicative, Monad)

liftSTM :: forall (schema :: Schema) {a}. STM a -> Edgy schema a
liftSTM = Edgy

getEdges ::
  forall
    (spec :: RelationSpec)
    {schema :: Schema}.
  (KnownSchema schema, Typeable spec, Typeable (Domain spec)) =>
  Node schema (Domain spec) ->
  STM [Node schema (Codomain spec)]
getEdges (Node ref) =
  readDBRef ref >>= \case
    Just (NodeImpl _ _ relations) ->
      case DMap.lookup (RelatedKey (typeRep :: TypeRep spec)) relations of
        Just (RelatedVal ns) -> return ns
        Nothing -> return []
    Nothing -> error "node not found"

modifyEdges ::
  forall (spec :: RelationSpec) {schema :: Schema}.
  (KnownSchema schema, Typeable spec, Typeable (Domain spec)) =>
  Node schema (Domain spec) ->
  ([Node schema (Codomain spec)] -> [Node schema (Codomain spec)]) ->
  STM ()
modifyEdges (Node ref) f =
  readDBRef ref >>= \case
    Just (NodeImpl uuid attrs relations) ->
      let relatedKey =
            RelatedKey
              (typeRep :: TypeRep spec)
          relations' = case DMap.lookup relatedKey relations of
            Just (RelatedVal targets) ->
              DMap.insert relatedKey (RelatedVal (f targets)) relations
            Nothing ->
              DMap.insert relatedKey (RelatedVal (f [])) relations
       in writeDBRef ref (NodeImpl uuid attrs relations')
    Nothing -> error "node not found"

bigBang :: KnownSchema schema => Edgy schema (Node schema Universe)
bigBang = Edgy $ do
  let ref = getDBRef (show UUID.nil)
  readDBRef ref >>= \case
    Just _ -> return (Node ref)
    Nothing -> Node <$> newDBRef (emptyNodeImpl UUID.nil)

newNode ::
  forall (typeName :: Symbol) {schema :: Schema}.
  (KnownSymbol typeName, HasNode schema (DataNode typeName)) =>
  Edgy schema (Node schema (DataNode typeName))
newNode = Edgy $ do
  uuid <- safeIOToSTM UUID.nextRandom
  node <- Node <$> newDBRef (emptyNodeImpl uuid)
  let universe = Node (getDBRef (show UUID.nil)) :: Node schema Universe
  modifyEdges @(ExistenceSpec typeName) universe (node :)
  modifyEdges @(UniversalSpec typeName) node (const [universe])
  return node

deleteNode ::
  forall (typeName :: Symbol) {schema :: Schema}.
  (KnownSymbol typeName, HasNode schema (DataNode typeName)) =>
  Node schema (DataNode typeName) ->
  Edgy schema ()
deleteNode node@(Node ref) = Edgy $ do
  foldRelations
    (Proxy @schema)
    ( \(_ :: Proxy relation) (_ :: Proxy inverse) delRemaining -> do
        case testEquality
          (typeRep @(Domain relation))
          (typeRep @(DataNode typeName)) of
          Just Refl -> do
            nodes <- getEdges @relation node
            forM_ nodes $ \n -> do
              modifyEdges @inverse n (filter (/= node))
          Nothing -> return ()
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
getAttribute (Node ref) = Edgy $ do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl _ attrs _) ->
      case DMap.lookup (AttributeKey (typeRep :: TypeRep attr)) attrs of
        Just (AttributeVal val) -> return val
        Nothing -> error "getAttribute: attr not found"
    Nothing -> error "getAttribute: node not found"

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
setAttribute (Node ref) value = Edgy $ do
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
    Nothing -> error "setAttribute: node not found"

getRelated ::
  forall
    (relation :: RelationId)
    {schema :: Schema}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}
    {n :: Cardinality}.
  (HasRelation schema relation spec inverse, n ~ CodomainCardinality spec) =>
  Node schema (Domain spec) ->
  Edgy schema (Numerous n (Node schema (Codomain spec)))
getRelated node = Edgy $ do
  listToNumerous @n <$> getEdges @spec node >>= \case
    Just result -> return result
    Nothing -> error "getRelated: bad cardinality"

isRelated ::
  forall
    (relation :: RelationId)
    {schema :: Schema}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema relation spec inverse =>
  Node schema (Domain spec) ->
  Node schema (Codomain spec) ->
  Edgy schema Bool
isRelated node target = Edgy $ elem target <$> getEdges @spec node

setRelated ::
  forall
    (relationName :: Symbol)
    {schema :: Schema}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}
    {n :: Cardinality}.
  ( HasRelation schema (Explicit relationName) spec inverse,
    n ~ CodomainCardinality spec
  ) =>
  Node schema (Domain spec) ->
  Numerous n (Node schema (Codomain spec)) ->
  Edgy schema ()
setRelated a target = Edgy $ do
  oldNodes <- getEdges @spec a
  let newNodes = numerousToList @n target
  modifyEdges @spec a (const newNodes)
  forM_ (oldNodes \\ newNodes) $ \b -> modifyEdges @inverse b (filter (/= a))
  forM_ (newNodes \\ oldNodes) $ \b -> modifyEdges @inverse b (a :)

addRelated ::
  forall
    (relationName :: Symbol)
    {schema :: Schema}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema (Explicit relationName) spec inverse =>
  Node schema (Domain spec) ->
  Node schema (Codomain spec) ->
  Edgy schema ()
addRelated a b = Edgy $ do
  modifyEdges @spec a (b :)
  modifyEdges @inverse b (a :)

removeRelated ::
  forall
    (relationName :: Symbol)
    {schema :: Schema}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema (Explicit relationName) spec inverse =>
  Node schema (Domain spec) ->
  Node schema (Codomain spec) ->
  Edgy schema ()
removeRelated a b = Edgy $ do
  modifyEdges @spec a (filter (/= b))
  modifyEdges @inverse b (filter (/= a))

clearRelated ::
  forall
    (relationName :: Symbol)
    {schema :: Schema}
    {spec :: RelationSpec}
    {inverse :: RelationSpec}.
  HasRelation schema (Explicit relationName) spec inverse =>
  Node schema (Domain spec) ->
  Edgy schema ()
clearRelated node = Edgy $ do
  nodes <- getEdges @spec node
  forM_ nodes $ \n -> do
    modifyEdges @inverse n (filter (/= node))
  modifyEdges @spec node (const [])
