{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Edgy
  ( Node,
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

import Cardinality (Cardinality, KnownCardinality (..), Numerous)
import qualified Data.Dependent.Map as DMap
import Data.Proxy (Proxy (..))
import Data.TCache
  ( STM,
    delDBRef,
    getDBRef,
    newDBRef,
    readDBRef,
    safeIOToSTM,
    writeDBRef,
  )
import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID
import GHC.TypeLits (Symbol)
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
    HasAttribute,
    HasNode,
    HasRelation,
    KnownSchema,
    NodeType (..),
    RelationId,
    RelationSpec,
    Schema,
  )
import Type.Reflection (TypeRep, typeRep)

bigBang :: KnownSchema schema => STM (Node schema Universe)
bigBang = do
  let ref = getDBRef (show UUID.nil)
  readDBRef ref >>= \case
    Just _ -> return (Node ref)
    Nothing -> Node <$> newDBRef (emptyNodeImpl UUID.nil)

newNode ::
  (HasNode schema nodeType, nodeType ~ DataNode n) =>
  STM (Node schema nodeType)
newNode = do
  uuid <- safeIOToSTM UUID.nextRandom
  Node <$> newDBRef (emptyNodeImpl uuid)

deleteNode ::
  (HasNode schema nodeType, nodeType ~ DataNode n) =>
  Node schema nodeType ->
  STM ()
deleteNode (Node ref) = delDBRef ref

getAttribute ::
  forall
    (name :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {attr :: AttributeSpec}.
  HasAttribute schema nodeType name attr =>
  Node schema nodeType ->
  STM (AttributeType attr)
getAttribute (Node ref) = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl _ attrs _) ->
      case DMap.lookup (AttributeKey (typeRep :: TypeRep attr)) attrs of
        Just (AttributeVal val) -> return val
        Nothing -> error "getAttr: attr not found"
    Nothing -> error "getAttr: node not found"

setAttribute ::
  forall
    (name :: Symbol)
    {schema :: Schema}
    {nodeType :: NodeType}
    {attr :: AttributeSpec}.
  HasAttribute schema nodeType name attr =>
  Node schema nodeType ->
  AttributeType attr ->
  STM ()
setAttribute (Node ref) value = do
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
    Nothing -> error "setAttr: node not found"

getRelated ::
  forall
    (relation :: RelationId)
    {schema :: Schema}
    {spec :: RelationSpec}
    {n :: Cardinality}.
  (HasRelation schema relation spec, n ~ CodomainCardinality spec) =>
  Node schema (Domain spec) ->
  STM (Numerous n (Node schema (Codomain spec)))
getRelated (Node ref) = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl _ _ relations) -> do
      let nodes = case DMap.lookup (RelatedKey (typeRep :: TypeRep spec)) relations of
            Just (RelatedVal ns) -> ns
            Nothing -> []
      case toCardinality (Proxy :: Proxy n) nodes of
        Just result -> return result
        Nothing -> error "getRelated: bad cardinality"
    Nothing -> error "getRelated: node not found"

isRelated ::
  forall (relation :: RelationId) {schema :: Schema} {spec :: RelationSpec}.
  HasRelation schema relation spec =>
  Node schema (Domain spec) ->
  Node schema (Codomain spec) ->
  STM Bool
isRelated (Node ref) target = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl _ _ relations) ->
      case DMap.lookup (RelatedKey (typeRep :: TypeRep spec)) relations of
        Just (RelatedVal ns) -> return (target `elem` ns)
        Nothing -> return False
    Nothing -> error "isRelated: node not found"

setRelated ::
  forall (relation :: RelationId) {schema :: Schema} {spec :: RelationSpec} {n :: Cardinality}.
  (HasRelation schema relation spec, n ~ CodomainCardinality spec) =>
  Node schema (Domain spec) ->
  Numerous n (Node schema (Codomain spec)) ->
  STM ()
setRelated (Node ref) target = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) ->
      writeDBRef ref $
        NodeImpl uuid attrs $
          DMap.insert
            (RelatedKey (typeRep :: TypeRep spec))
            (RelatedVal (fromCardinality (Proxy :: Proxy n) target))
            relations
    Nothing -> error "setRelation: node not found"

addRelated ::
  forall (relation :: RelationId) {schema :: Schema} {spec :: RelationSpec}.
  HasRelation schema relation spec =>
  Node schema (Domain spec) ->
  Node schema (Codomain spec) ->
  STM ()
addRelated (Node ref) target = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) -> do
      let relatedKey =
            RelatedKey
              (typeRep :: TypeRep spec)
          relations' = case DMap.lookup relatedKey relations of
            Just (RelatedVal targets) ->
              DMap.insert relatedKey (RelatedVal (target : targets)) relations
            Nothing ->
              DMap.insert relatedKey (RelatedVal [target]) relations
      writeDBRef ref (NodeImpl uuid attrs relations')
    Nothing -> error "addToRelation: node not found"

removeRelated ::
  forall (relation :: RelationId) {schema :: Schema} {spec :: RelationSpec}.
  HasRelation schema relation spec =>
  Node schema (Domain spec) ->
  Node schema (Codomain spec) ->
  STM ()
removeRelated (Node ref) target = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) -> do
      let relatedKey =
            RelatedKey
              (typeRep :: TypeRep spec)
          relations' = case DMap.lookup relatedKey relations of
            Just (RelatedVal targets) ->
              DMap.insert relatedKey (RelatedVal (filter (/= target) targets)) relations
            Nothing -> relations
      writeDBRef ref (NodeImpl uuid attrs relations')
    Nothing -> error "removeFromRelation: node not found"

clearRelated ::
  forall (relation :: RelationId) {schema :: Schema} {spec :: RelationSpec}.
  HasRelation schema relation spec =>
  Node schema (Domain spec) ->
  STM ()
clearRelated (Node ref) = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) -> do
      let relatedKey =
            RelatedKey
              (typeRep :: TypeRep spec)
          relations' = DMap.insert relatedKey (RelatedVal []) relations
      writeDBRef ref (NodeImpl uuid attrs relations')
    Nothing -> error "clearRelation: node not found"
