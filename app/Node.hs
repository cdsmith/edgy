{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}

module Node where

import Cardinality (Cardinality, KnownCardinality (..), Numerous)
import Data.Binary (Binary (..))
import qualified Data.Binary as Binary
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.GADT.Compare (GCompare (..), GEq (..), GOrdering (..))
import Data.Kind (Type)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import Data.TCache
  ( DBRef,
    STM,
    delDBRef,
    getDBRef,
    newDBRef,
    readDBRef,
    safeIOToSTM,
    writeDBRef,
  )
import Data.TCache.DefaultPersistence
  ( Indexable (key),
    Serializable (deserialize, serialize),
  )
import Data.Type.Equality ((:~:) (..))
import Data.Typeable (Typeable)
import Data.UUID (UUID)
import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID
import GHC.TypeLits (Symbol)
import Schema
  ( AttributeSpec,
    AttributeType,
    Codomain,
    CodomainCardinality,
    Domain,
    HasAttribute,
    HasNode,
    HasRelation,
    KnownSchema (..),
    NodeType (..),
    Relation,
    Schema,
  )
import Type.Reflection (SomeTypeRep (..), TypeRep, typeRep)
import Type.Reflection.Unsafe (typeRepFingerprint)

type Node :: Schema -> NodeType -> Type
newtype Node schema nodeType = Node (DBRef (NodeImpl schema nodeType))
  deriving (Eq, Ord)

instance
  (KnownSchema schema, Typeable nodeType) =>
  Binary (Node schema nodeType)
  where
  put (Node ref) = put (show ref)
  get = Node . read <$> get

type AttributeKey :: Schema -> AttributeSpec -> Type
data AttributeKey schema attr where
  AttributeKey ::
    TypeRep attr ->
    AttributeKey schema attr

instance Eq (AttributeKey schema attr) where
  AttributeKey a == AttributeKey b = SomeTypeRep a == SomeTypeRep b

instance Ord (AttributeKey schema attr) where
  compare (AttributeKey a) (AttributeKey b) = compare (SomeTypeRep a) (SomeTypeRep b)

instance GEq (AttributeKey schema) where
  geq (AttributeKey a) (AttributeKey b) = case geq a b of
    Just Refl -> Just Refl
    Nothing -> Nothing

instance GCompare (AttributeKey schema) where
  gcompare (AttributeKey a) (AttributeKey b) = case gcompare a b of
    GLT -> GLT
    GEQ -> GEQ
    GGT -> GGT

type AttributeVal :: Schema -> AttributeSpec -> Type
data AttributeVal schema attr where
  AttributeVal :: Binary (AttributeType attr) => AttributeType attr -> AttributeVal schema attr

instance Binary (AttributeType attr) => Binary (AttributeVal schema attr) where
  put (AttributeVal x) = put x
  get = AttributeVal <$> get

type RelatedKey :: Schema -> Relation -> Type
data RelatedKey schema relation where
  RelatedKey :: TypeRep relation -> RelatedKey schema relation

instance Eq (RelatedKey schema t) where
  RelatedKey a == RelatedKey b = SomeTypeRep a == SomeTypeRep b

instance Ord (RelatedKey schema t) where
  compare (RelatedKey a) (RelatedKey b) =
    compare (SomeTypeRep a) (SomeTypeRep b)

instance GEq (RelatedKey schema) where
  geq (RelatedKey a) (RelatedKey b) = case geq a b of
    Just Refl -> Just Refl
    Nothing -> Nothing

instance GCompare (RelatedKey schema) where
  gcompare (RelatedKey a) (RelatedKey b) = case gcompare a b of
    GLT -> GLT
    GEQ -> GEQ
    GGT -> GGT

type RelatedVal :: Schema -> Relation -> Type
data RelatedVal schema relation where
  RelatedVal ::
    [Node schema (Codomain relation)] ->
    RelatedVal schema relation

instance
  (KnownSchema schema, Typeable (Codomain relation)) =>
  Binary (RelatedVal schema relation)
  where
  put (RelatedVal ns) = put ns
  get = RelatedVal <$> get

type NodeImpl :: Schema -> NodeType -> Type
data NodeImpl schema nodeType
  = NodeImpl
      UUID
      (DMap (AttributeKey schema) (AttributeVal schema))
      (DMap (RelatedKey schema) (RelatedVal schema))

instance Indexable (NodeImpl schema nodeType) where
  key (NodeImpl uuid _ _) = show uuid

instance KnownSchema schema => Serializable (NodeImpl schema nodeType) where
  serialize = Binary.encode
  deserialize = Binary.decode

instance
  KnownSchema schema =>
  Binary (NodeImpl schema nodeType)
  where
  put (NodeImpl uuid attrs relations) = do
    put uuid

    put $
      foldAttributes
        (Proxy :: Proxy schema)
        ( \(_ :: Proxy attr) m ->
            let tr = typeRep :: TypeRep attr
                k = AttributeKey tr
             in case DMap.lookup k attrs of
                  Just (AttributeVal v) ->
                    Map.insert
                      (Binary.encode (typeRepFingerprint tr, show tr))
                      (Binary.encode v)
                      m
                  Nothing -> m
        )
        mempty

    put $
      foldRelations
        (Proxy :: Proxy schema)
        ( \(_ :: Proxy relation) m ->
            let tr = typeRep :: TypeRep relation
                k = RelatedKey tr
             in case DMap.lookup k relations of
                  Just (RelatedVal ns) ->
                    Map.insert
                      (Binary.encode (typeRepFingerprint tr, show tr))
                      (Binary.encode ns)
                      m
                  Nothing -> m
        )
        mempty

  get = do
    uuid <- get

    attrMap <- get
    let attrs =
          foldAttributes
            (Proxy :: Proxy schema)
            ( \(_ :: Proxy attr) m ->
                let tr = typeRep :: TypeRep attr
                    k = AttributeKey tr
                 in case Map.lookup
                      (Binary.encode (typeRepFingerprint tr, show tr))
                      attrMap of
                      Just val -> DMap.insert k (AttributeVal (Binary.decode val)) m
                      Nothing -> m
            )
            DMap.empty

    relMap <- get
    let relations =
          foldRelations
            (Proxy :: Proxy schema)
            ( \(_ :: Proxy relation) m ->
                let tr = typeRep :: TypeRep relation
                    k = RelatedKey tr
                 in case Map.lookup
                      (Binary.encode (typeRepFingerprint tr, show tr))
                      relMap of
                      Just val -> DMap.insert k (RelatedVal (Binary.decode val)) m
                      Nothing -> m
            )
            DMap.empty

    pure (NodeImpl uuid attrs relations)

emptyNodeImpl :: UUID -> NodeImpl schema nodeType
emptyNodeImpl uuid = NodeImpl uuid DMap.empty DMap.empty

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
  Proxy name ->
  Node schema nodeType ->
  STM (AttributeType attr)
getAttribute _ (Node ref) = do
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
  Proxy name ->
  Node schema nodeType ->
  AttributeType attr ->
  STM ()
setAttribute _ (Node ref) value = do
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
  forall (schema :: Schema) (relation :: Relation) (n :: Cardinality).
  ( HasRelation schema relation,
    n ~ CodomainCardinality relation
  ) =>
  Proxy relation ->
  Node schema (Domain relation) ->
  STM (Numerous n (Node schema (Codomain relation)))
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

isRelated ::
  forall (schema :: Schema) (relation :: Relation).
  HasRelation schema relation =>
  Proxy relation ->
  Node schema (Domain relation) ->
  Node schema (Codomain relation) ->
  STM Bool
isRelated _ (Node ref) target = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl _ _ relations) ->
      case DMap.lookup (RelatedKey (typeRep :: TypeRep relation)) relations of
        Just (RelatedVal ns) -> return (target `elem` ns)
        Nothing -> return False
    Nothing -> error "isRelated: node not found"

setRelated ::
  forall (schema :: Schema) (relation :: Relation) (n :: Cardinality).
  (HasRelation schema relation, n ~ CodomainCardinality relation) =>
  Proxy relation ->
  Node schema (Domain relation) ->
  Numerous n (Node schema (Codomain relation)) ->
  STM ()
setRelated _ (Node ref) target = do
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

addRelated ::
  forall (schema :: Schema) (relation :: Relation).
  HasRelation schema relation =>
  Proxy relation ->
  Node schema (Domain relation) ->
  Node schema (Codomain relation) ->
  STM ()
addRelated _ (Node ref) target = do
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

removeRelated ::
  forall (schema :: Schema) (relation :: Relation).
  HasRelation schema relation =>
  Proxy relation ->
  Node schema (Domain relation) ->
  Node schema (Codomain relation) ->
  STM ()
removeRelated _ (Node ref) target = do
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

clearRelated ::
  forall (schema :: Schema) (relation :: Relation).
  HasRelation schema relation =>
  Proxy relation ->
  Node schema (Domain relation) ->
  STM ()
clearRelated _ (Node ref) = do
  nodeImpl <- readDBRef ref
  case nodeImpl of
    Just (NodeImpl uuid attrs relations) -> do
      let relatedKey =
            RelatedKey
              (typeRep :: TypeRep relation)
          relations' = DMap.insert relatedKey (RelatedVal []) relations
      writeDBRef ref (NodeImpl uuid attrs relations')
    Nothing -> error "clearRelation: node not found"
