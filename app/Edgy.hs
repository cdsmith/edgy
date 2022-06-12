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
  ( Edgy,
    runEdgy,
    liftSTM,
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
  )
where

import Cardinality (Cardinality (..), KnownCardinality (..), Numerous)
import qualified Data.Dependent.Map as DMap
import Data.Kind (Type)
import Data.TCache
  ( STM,
    delDBRef,
    getDBRef,
    newDBRef,
    readDBRef,
    safeIOToSTM,
    writeDBRef,
  )
import Data.Typeable (Typeable)
import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID
import GHC.TypeLits (KnownSymbol, Symbol)
import Node
  ( AttributeKey (..),
    AttributeVal (..),
    Node (..),
    NodeImpl (..),
    RelatedKey (..),
    RelatedVal (..),
    emptyNodeImpl,
  )
import Schema
  ( AttributeSpec,
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
    UniversalSpec,
  )
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
  (HasNode schema nodeType, nodeType ~ DataNode n) =>
  Node schema nodeType ->
  Edgy schema ()
deleteNode (Node ref) = Edgy $ delDBRef ref

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
    Nothing -> error "getAttribute: node not found"

getRelated ::
  forall
    (relation :: RelationId)
    {schema :: Schema}
    {spec :: RelationSpec}
    {n :: Cardinality}.
  (HasRelation schema relation spec, n ~ CodomainCardinality spec) =>
  Node schema (Domain spec) ->
  Edgy schema (Numerous n (Node schema (Codomain spec)))
getRelated node = Edgy $ do
  listToNumerous @n <$> getEdges @spec node >>= \case
    Just result -> return result
    Nothing -> error "getRelated: bad cardinality"

isRelated ::
  forall (relation :: RelationId) {schema :: Schema} {spec :: RelationSpec}.
  HasRelation schema relation spec =>
  Node schema (Domain spec) ->
  Node schema (Codomain spec) ->
  Edgy schema Bool
isRelated node target = Edgy $ elem target <$> getEdges @spec node

setRelated ::
  forall
    (relation :: RelationId)
    {schema :: Schema}
    {spec :: RelationSpec}
    {n :: Cardinality}.
  (HasRelation schema relation spec, n ~ CodomainCardinality spec) =>
  Node schema (Domain spec) ->
  Numerous n (Node schema (Codomain spec)) ->
  Edgy schema ()
setRelated node target = Edgy $ do
  modifyEdges @spec node (const (numerousToList @n target))

addRelated ::
  forall (relation :: RelationId) {schema :: Schema} {spec :: RelationSpec}.
  HasRelation schema relation spec =>
  Node schema (Domain spec) ->
  Node schema (Codomain spec) ->
  Edgy schema ()
addRelated node target = Edgy $ modifyEdges @spec node (target :)

removeRelated ::
  forall (relation :: RelationId) {schema :: Schema} {spec :: RelationSpec}.
  HasRelation schema relation spec =>
  Node schema (Domain spec) ->
  Node schema (Codomain spec) ->
  Edgy schema ()
removeRelated node target = Edgy $ modifyEdges @spec node (filter (/= target))

clearRelated ::
  forall (relation :: RelationId) {schema :: Schema} {spec :: RelationSpec}.
  HasRelation schema relation spec =>
  Node schema (Domain spec) ->
  Edgy schema ()
clearRelated node = Edgy $ modifyEdges @spec node (const [])
