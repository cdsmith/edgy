{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Edgy.Node where

import Data.Binary (Binary)
import qualified Data.Binary as Binary
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.GADT.Compare (GCompare (..), GEq (..), GOrdering (..))
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (..))
import Data.Typeable (Typeable)
import Data.UUID (UUID)
import Edgy.Schema
  ( AttributeName,
    AttributeSpec,
    AttributeType,
    KnownSchema (..),
    NodeType (..),
    RelationName,
    RelationSpec (..),
    Schema,
    Target,
  )
import GHC.TypeLits (KnownSymbol, symbolVal)
import PersistentSTM (DBRef, DBStorable (..))
import Type.Reflection (SomeTypeRep (..), TypeRep, typeRep)

newtype Node (schema :: Schema) (nodeType :: NodeType)
  = Node (DBRef (NodeImpl schema nodeType))
  deriving (Eq, Ord)

instance
  (KnownSchema schema, Typeable nodeType) =>
  DBStorable (Node schema nodeType)
  where
  encode (Node ref) = encode ref
  decode db bs = Node <$> decode db bs

data AttributeKey (schema :: Schema) (attr :: AttributeSpec) where
  AttributeKey ::
    TypeRep attr ->
    AttributeKey schema attr

instance Eq (AttributeKey schema attr) where
  AttributeKey a == AttributeKey b = SomeTypeRep a == SomeTypeRep b

instance Ord (AttributeKey schema attr) where
  compare (AttributeKey a) (AttributeKey b) =
    compare (SomeTypeRep a) (SomeTypeRep b)

instance GEq (AttributeKey schema) where
  geq (AttributeKey a) (AttributeKey b) = case geq a b of
    Just Refl -> Just Refl
    Nothing -> Nothing

instance GCompare (AttributeKey schema) where
  gcompare (AttributeKey a) (AttributeKey b) = case gcompare a b of
    GLT -> GLT
    GEQ -> GEQ
    GGT -> GGT

data AttributeVal (schema :: Schema) (attr :: AttributeSpec) where
  AttributeVal ::
    Binary (AttributeType attr) =>
    AttributeType attr ->
    AttributeVal schema attr

instance Binary (AttributeType attr) => Binary (AttributeVal schema attr) where
  put (AttributeVal x) = Binary.put x
  get = AttributeVal <$> Binary.get

data RelatedKey (schema :: Schema) (relation :: RelationSpec) where
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

data Nodes (schema :: Schema) (relation :: RelationSpec)
  = Nodes UUID [Node schema (Target relation)]

relatedKey ::
  forall (relation :: RelationSpec).
  KnownSymbol (RelationName relation) =>
  UUID ->
  Proxy relation ->
  String
relatedKey uuid _ =
  show uuid ++ "." ++ symbolVal (Proxy @(RelationName relation))

instance
  (KnownSchema schema, Typeable relation, Typeable (Target relation)) =>
  DBStorable (Nodes schema relation)
  where
  encode (Nodes uuid nodes) = Binary.encode (uuid, map encode nodes)
  decode db bs = do
    let (uuid, nodes) = Binary.decode bs
    Nodes uuid <$> mapM (decode db) nodes

data RelatedVal schema (relation :: RelationSpec) where
  RelatedVal ::
    DBRef (Nodes schema relation) ->
    RelatedVal schema relation

instance
  ( KnownSchema schema,
    Typeable relation,
    KnownSymbol (RelationName relation),
    Typeable (Target relation)
  ) =>
  DBStorable (RelatedVal schema relation)
  where
  encode (RelatedVal ref) = encode ref
  decode db bs = RelatedVal <$> decode db bs

data NodeImpl (schema :: Schema) (nodeType :: NodeType)
  = NodeImpl
      UUID
      (DMap (AttributeKey schema) (AttributeVal schema))
      (DMap (RelatedKey schema) (RelatedVal schema))

instance
  (KnownSchema schema, Typeable nodeType) =>
  DBStorable (NodeImpl schema nodeType)
  where
  encode (NodeImpl uuid attrs _) =
    let attrMap =
          foldAttributes
            (Proxy :: Proxy schema)
            (Proxy :: Proxy nodeType)
            ( \(_ :: Proxy attr) m ->
                let n = symbolVal (Proxy @(AttributeName attr))
                    tr = typeRep @(AttributeType attr)
                    k = AttributeKey (typeRep @attr)
                 in case DMap.lookup k attrs of
                      Just (AttributeVal v) ->
                        Map.insert
                          (Binary.encode (n, tr))
                          (Binary.encode v)
                          m
                      Nothing -> m
            )
            mempty
     in Binary.encode (uuid, attrMap)

  decode _ bs = do
    let (uuid, attrMap) = Binary.decode bs
    let attrs =
          foldAttributes
            (Proxy :: Proxy schema)
            (Proxy :: Proxy nodeType)
            ( \(_ :: Proxy attr) m ->
                let n = symbolVal (Proxy @(AttributeName attr))
                    tr = typeRep @(AttributeType attr)
                    k = AttributeKey (typeRep @attr)
                 in case Map.lookup
                      (Binary.encode (n, tr))
                      attrMap of
                      Just val ->
                        DMap.insert
                          k
                          (AttributeVal (Binary.decode val))
                          m
                      Nothing -> m
            )
            DMap.empty
    pure (NodeImpl uuid attrs DMap.empty)

emptyNodeImpl :: UUID -> NodeImpl schema nodeType
emptyNodeImpl uuid = NodeImpl uuid DMap.empty DMap.empty
