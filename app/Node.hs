{-# LANGUAGE AllowAmbiguousTypes #-}
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

import Data.Binary (Binary (..))
import qualified Data.Binary as Binary
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.GADT.Compare (GCompare (..), GEq (..), GOrdering (..))
import Data.Kind (Type)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import Data.TCache (DBRef)
import Data.TCache.DefaultPersistence (Indexable (..), Serializable (..))
import Data.Type.Equality ((:~:) (..))
import Data.Typeable (Typeable)
import Data.UUID (UUID)
import Schema
  ( AttributeSpec,
    AttributeType,
    Codomain,
    KnownSchema (..),
    NodeType (..),
    RelationSpec (..),
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

type RelatedKey :: Schema -> RelationSpec -> Type
data RelatedKey schema relation where
  RelatedKey :: TypeRep relation -> RelatedKey schema relation

instance Eq (RelatedKey schema relation) where
  RelatedKey a == RelatedKey b = SomeTypeRep a == SomeTypeRep b

instance Ord (RelatedKey schema relation) where
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

type RelatedVal :: Schema -> RelationSpec -> Type
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
