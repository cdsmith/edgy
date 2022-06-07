{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Schema
  ( Schema,
    SchemaDef (..),
    NodeType (..),
    Relation (..),
    Related (..),
    Attribute (..),
    Node,
    bigBang,
    newNode,
    deleteNode,
    getAttr,
    setAttr,
    getRelated,
    addToRelation,
    removeFromRelation,
    setRelation,
    clearRelation,
  )
where

import Cardinality (Cardinality (..), KnownCardinality (..), Numerous)
import Control.Concurrent.STM (STM)
import Data.Binary (Binary (..))
import qualified Data.Binary as Binary
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.GADT.Compare (GCompare (..), GEq (..), GOrdering (..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.TCache (DBRef, delDBRef, newDBRef, readDBRef, safeIOToSTM, writeDBRef)
import Data.TCache.DefaultPersistence (Indexable (..), Serializable (..))
import Data.Type.Equality ((:~:) (..))
import Data.Typeable (Typeable)
import Data.UUID (UUID)
import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID
import GHC.TypeLits (ErrorMessage (Text), KnownSymbol, Symbol, TypeError)
import Type.Reflection (SomeTypeRep (..), TypeRep, typeRep)

type Schema = [SchemaDef]

data SchemaDef where
  AttrDef :: NodeType -> Symbol -> Type -> SchemaDef
  RelationDef ::
    NodeType ->
    Cardinality ->
    Symbol ->
    NodeType ->
    Cardinality ->
    SchemaDef

type LookupResult :: forall k. k -> Type
data LookupResult a where
  NotFound :: LookupResult a
  Found :: a -> LookupResult a

type IsFound :: LookupResult k -> Bool
type family IsFound r where
  IsFound (Found _) = True
  IsFound NotFound = False

type LookupValue :: LookupResult k -> k
type family LookupValue r where
  LookupValue (Found a) = a
  LookupValue NotFound = TypeError (Text "LookupValue: NotFound")

type LookupAttr :: Schema -> NodeType -> Symbol -> LookupResult Type
type family LookupAttr schema nodeType attrName where
  LookupAttr '[] _ _ = NotFound
  LookupAttr (AttrDef nodeType attrName t ': rest) nodeType attrName = Found t
  LookupAttr (_ ': rest) nodeType attrName = LookupAttr rest nodeType attrName

data NamedRelationInfo where
  NamedRelationInfo ::
    NodeType ->
    Cardinality ->
    NodeType ->
    Cardinality ->
    NamedRelationInfo

type NamedRelationInfo_Domain :: NamedRelationInfo -> NodeType
type family NamedRelationInfo_Domain def where
  NamedRelationInfo_Domain ('NamedRelationInfo a _ _ _) = a

type NamedRelationInfo_DomainCardinality :: NamedRelationInfo -> Cardinality
type family NamedRelationInfo_DomainCardinality def where
  NamedRelationInfo_DomainCardinality ('NamedRelationInfo _ na _ _) = na

type NamedRelationInfo_Codomain :: NamedRelationInfo -> NodeType
type family NamedRelationInfo_Codomain def where
  NamedRelationInfo_Codomain ('NamedRelationInfo _ _ b _) = b

type NamedRelationInfo_CodomainCardinality :: NamedRelationInfo -> Cardinality
type family NamedRelationInfo_CodomainCardinality def where
  NamedRelationInfo_CodomainCardinality ('NamedRelationInfo _ _ _ nb) = nb

type LookupRelation :: Schema -> Symbol -> LookupResult NamedRelationInfo
type family LookupRelation schema name where
  LookupRelation '[] _ = NotFound
  LookupRelation (RelationDef a na name b nb ': rest) name =
    Found ('NamedRelationInfo a na b nb)
  LookupRelation (_ ': rest) name = LookupRelation rest name

data NodeType where
  Universe :: NodeType
  DataNode :: Type -> NodeType

data Relation where
  NamedRelation :: Symbol -> Relation
  Inverse :: Symbol -> Relation
  Existence :: Type -> Relation

type Related :: Schema -> Relation -> Constraint
class Related schema relation where
  type Domain schema relation :: NodeType
  type Codomain schema relation :: NodeType
  type DomainCardinality schema relation :: Cardinality
  type CodomainCardinality schema relation :: Cardinality

instance
  Related schema (NamedRelation name) =>
  Related schema (Inverse name)
  where
  type Domain schema (Inverse name) = Codomain schema (NamedRelation name)
  type Codomain schema (Inverse name) = Domain schema (NamedRelation name)
  type
    DomainCardinality schema (Inverse name) =
      CodomainCardinality schema (NamedRelation name)
  type
    CodomainCardinality schema (Inverse name) =
      DomainCardinality schema (NamedRelation name)

instance forall schema a. Related schema (Existence a) where
  type Domain schema (Existence a) = Universe
  type Codomain schema (Existence a) = DataNode a
  type DomainCardinality schema (Existence a) = One
  type CodomainCardinality schema (Existence a) = Many

instance
  forall schema name.
  IsFound (LookupRelation schema name) ~ True =>
  Related schema (NamedRelation name)
  where
  type
    Domain schema (NamedRelation name) =
      NamedRelationInfo_Domain (LookupValue (LookupRelation schema name))
  type
    Codomain schema (NamedRelation name) =
      NamedRelationInfo_Codomain (LookupValue (LookupRelation schema name))
  type
    DomainCardinality schema (NamedRelation name) =
      NamedRelationInfo_DomainCardinality
        (LookupValue (LookupRelation schema name))
  type
    CodomainCardinality schema (NamedRelation name) =
      NamedRelationInfo_CodomainCardinality
        (LookupValue (LookupRelation schema name))

type Attribute :: Schema -> NodeType -> Symbol -> Constraint
class Attribute schema nodeType attrName where
  type ValueType schema nodeType attrName :: Type

instance
  IsFound (LookupAttr schema nodeType attrName) ~ True =>
  Attribute schema nodeType attrName
  where
  type
    ValueType schema nodeType attrName =
      LookupValue (LookupAttr schema nodeType attrName)

type Node :: Schema -> NodeType -> Type
newtype Node schema nodeType = Node (DBRef (NodeImpl schema nodeType))
  deriving (Eq, Ord)

instance
  (Typeable schema, Typeable nodeType) =>
  Binary (Node schema nodeType)
  where
  put (Node ref) = put (show ref)
  get = Node . read <$> get

type AttrKey :: Schema -> NodeType -> Type -> Type
data AttrKey schema nodeType t where
  AttrKey ::
    Attribute schema nodeType attrName =>
    TypeRep attrName ->
    AttrKey schema nodeType (ValueType schema nodeType attrName)

instance Eq (AttrKey schema nodeType t) where
  AttrKey a == AttrKey b = SomeTypeRep a == SomeTypeRep b

instance Ord (AttrKey schema nodeType t) where
  compare (AttrKey a) (AttrKey b) = compare (SomeTypeRep a) (SomeTypeRep b)

instance GEq (AttrKey schema nodeType) where
  geq (AttrKey a) (AttrKey b) = case geq a b of
    Just Refl -> Just Refl
    Nothing -> Nothing

instance GCompare (AttrKey schema nodeType) where
  gcompare (AttrKey a) (AttrKey b) = case gcompare a b of
    GLT -> GLT
    GEQ -> GEQ
    GGT -> GGT

type AttrVal :: Schema -> Type -> Type
data AttrVal schema a where
  AttrVal :: Binary a => a -> AttrVal schema a

type RelatedKey :: Schema -> NodeType -> Relation -> Type
data RelatedKey schema nodeType relation where
  RelatedKey :: TypeRep relation -> RelatedKey schema nodeType relation

instance Eq (RelatedKey schema nodeType t) where
  RelatedKey a == RelatedKey b = SomeTypeRep a == SomeTypeRep b

instance Ord (RelatedKey schema nodeType t) where
  compare (RelatedKey a) (RelatedKey b) =
    compare (SomeTypeRep a) (SomeTypeRep b)

instance GEq (RelatedKey schema nodeType) where
  geq (RelatedKey a) (RelatedKey b) = case geq a b of
    Just Refl -> Just Refl
    Nothing -> Nothing

instance GCompare (RelatedKey schema nodeType) where
  gcompare (RelatedKey a) (RelatedKey b) = case gcompare a b of
    GLT -> GLT
    GEQ -> GEQ
    GGT -> GGT

type RelatedVal :: Schema -> Relation -> Type
data RelatedVal schema relation where
  RelatedVal ::
    Related schema relation =>
    [Node schema (Codomain schema relation)] ->
    RelatedVal schema relation

type NodeImpl :: Schema -> NodeType -> Type
data NodeImpl schema nodeType
  = NodeImpl
      UUID
      (DMap (AttrKey schema nodeType) (AttrVal schema))
      (DMap (RelatedKey schema nodeType) (RelatedVal schema))

instance Indexable (NodeImpl schema nodeType) where
  key (NodeImpl uuid _ _) = show uuid

instance Serializable (NodeImpl schema nodeType) where
  serialize = Binary.encode
  deserialize = Binary.decode

instance Binary (NodeImpl schema nodeType) where
  put (NodeImpl uuid attrs relations) = do
    Binary.put uuid
    Binary.put attrs
    Binary.put relations
  get = NodeImpl <$> Binary.get <*> Binary.get <*> Binary.get

instance Binary (DMap f g) where
  get = return DMap.empty
  put _ = return ()

emptyNodeImpl :: UUID -> NodeImpl schema nodeType
emptyNodeImpl uuid = NodeImpl uuid DMap.empty DMap.empty

bigBang :: Typeable schema => STM (Node schema Universe)
bigBang = do
  Node <$> newDBRef (emptyNodeImpl UUID.nil)

newNode :: (Typeable schema, Typeable a) => STM (Node schema (DataNode a))
newNode = do
  uuid <- safeIOToSTM UUID.nextRandom
  Node <$> newDBRef (emptyNodeImpl uuid)

deleteNode ::
  (Typeable schema, Typeable a) => Node schema (DataNode a) -> STM ()
deleteNode (Node ref) = delDBRef ref

getAttr ::
  forall schema nodeType attrName.
  ( Typeable schema,
    Typeable nodeType,
    KnownSymbol attrName,
    Attribute schema nodeType attrName
  ) =>
  Proxy attrName ->
  Node schema nodeType ->
  STM (ValueType schema nodeType attrName)
getAttr _ (Node ref) = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl _ attrs _) ->
      case DMap.lookup (AttrKey (typeRep :: TypeRep attrName)) attrs of
        Just (AttrVal val) -> return val
        Nothing -> error "getAttr: attr not found"
    Nothing -> error "getAttr: node not found"

setAttr ::
  forall schema nodeType attrName.
  ( Typeable schema,
    Typeable nodeType,
    KnownSymbol attrName,
    Attribute schema nodeType attrName,
    Binary (LookupValue (LookupAttr schema nodeType attrName))
  ) =>
  Proxy attrName ->
  Node schema nodeType ->
  ValueType schema nodeType attrName ->
  STM ()
setAttr _ (Node ref) value = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) ->
      writeDBRef
        ref
        ( NodeImpl
            uuid
            ( DMap.insert
                (AttrKey (typeRep :: TypeRep attrName))
                (AttrVal value)
                attrs
            )
            relations
        )
    Nothing -> error "setAttr: node not found"

getRelated ::
  forall (schema :: Schema) (nodeType :: NodeType) (relation :: Relation) (n :: Cardinality).
  ( Typeable schema,
    Typeable relation,
    Related schema relation,
    nodeType ~ Domain schema relation,
    Typeable nodeType,
    KnownCardinality n,
    n ~ CodomainCardinality schema relation
  ) =>
  Proxy relation ->
  Node schema (Domain schema relation) ->
  STM (Numerous n (Node schema (Codomain schema relation)))
getRelated _ (Node ref) = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl _ _ relations) -> do
      let nodes = case DMap.lookup (RelatedKey (typeRep :: TypeRep relation)) relations of
            Just (RelatedVal ns) -> ns
            Nothing -> []
      case toCardinality (Proxy :: Proxy n) nodes of
        Just result -> return result
        Nothing -> error "getRelated: bad cardinality"
    Nothing -> error "getRelated: node not found"

addToRelation ::
  forall (schema :: Schema) (relation :: Relation).
  ( Typeable schema,
    Typeable relation,
    Related schema relation,
    Typeable (Domain schema relation)
  ) =>
  Proxy relation ->
  Node schema (Domain schema relation) ->
  Node schema (Codomain schema relation) ->
  STM ()
addToRelation _ (Node ref) target = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) -> do
      let relatedKey =
            RelatedKey
              (typeRep :: TypeRep relation)
          relations' = case DMap.lookup relatedKey relations of
            Just (RelatedVal targets) ->
              DMap.insert relatedKey (RelatedVal (target : targets)) relations
            Nothing ->
              DMap.insert relatedKey (RelatedVal [target]) relations
      writeDBRef ref (NodeImpl uuid attrs relations')
    Nothing -> error "addToRelation: node not found"

removeFromRelation ::
  forall (schema :: Schema) (relation :: Relation).
  ( Typeable schema,
    Typeable relation,
    Related schema relation,
    Typeable (Domain schema relation)
  ) =>
  Node schema (Domain schema relation) ->
  Proxy relation ->
  Node schema (Codomain schema relation) ->
  STM ()
removeFromRelation (Node ref) _ target = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) -> do
      let relatedKey =
            RelatedKey
              (typeRep :: TypeRep relation)
          relations' = case DMap.lookup relatedKey relations of
            Just (RelatedVal targets) ->
              DMap.insert relatedKey (RelatedVal (filter (/= target) targets)) relations
            Nothing -> relations
      writeDBRef ref (NodeImpl uuid attrs relations')
    Nothing -> error "removeFromRelation: node not found"

setRelation ::
  forall (schema :: Schema) (relation :: Relation) (n :: Cardinality).
  ( Typeable schema,
    Typeable relation,
    Related schema relation,
    Typeable (Domain schema relation),
    KnownCardinality n,
    n ~ CodomainCardinality schema relation
  ) =>
  Related schema relation =>
  Node schema (Domain schema relation) ->
  Proxy relation ->
  Numerous n (Node schema (Codomain schema relation)) ->
  STM ()
setRelation (Node ref) _ target = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) ->
      writeDBRef ref $
        NodeImpl uuid attrs $
          DMap.insert
            (RelatedKey (typeRep :: TypeRep relation))
            (RelatedVal (fromCardinality (Proxy :: Proxy n) target))
            relations
    Nothing -> error "setRelation: node not found"

clearRelation ::
  forall (schema :: Schema) (relation :: Relation).
  ( Typeable schema,
    Typeable relation,
    Related schema relation,
    Typeable (Domain schema relation)
  ) =>
  Node schema (Domain schema relation) ->
  Proxy relation ->
  STM ()
clearRelation (Node ref) _ = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) -> do
      let relatedKey =
            RelatedKey
              (typeRep :: TypeRep relation)
          relations' = DMap.insert relatedKey (RelatedVal []) relations
      writeDBRef ref (NodeImpl uuid attrs relations')
    Nothing -> error "clearRelation: node not found"
