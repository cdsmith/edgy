{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Schema
  ( -- * Nodes
    NodeType (..),

    -- * Attributes
    AttributeSpec (..),
    AttributeType,

    -- * Relations
    Relation (..),
    Domain,
    DomainCardinality,
    Codomain,
    CodomainCardinality,
    Inverse,

    -- * Schema
    Schema,
    SchemaDef (..),
    KnownSchema (..),
    HasNode,
    HasRelation,
    HasAttribute,

    -- * Schema folds
    AttributeFold,
    RelationFold,
  )
where

import Cardinality (Cardinality (..), KnownCardinality)
import Data.Binary (Binary (..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.Typeable (Typeable)
import Data.Void (Void)
import GHC.TypeLits (ErrorMessage (..), KnownSymbol, Symbol, TypeError)

-- The kind for node types.  There is exactly one node of the type 'Universe',
-- as well as any number of 'DataNode' types created by the application.
data NodeType where
  Universe :: NodeType
  DataNode :: Symbol -> NodeType

data AttributeSpec where
  Attribute :: NodeType -> Symbol -> Type -> AttributeSpec

type AttributeType :: AttributeSpec -> Type
type family AttributeType attr where
  AttributeType ('Attribute _ _ t) = t

data Relation where
  Directed ::
    NodeType ->
    Cardinality ->
    Symbol ->
    Cardinality ->
    NodeType ->
    Relation
  Symmetric :: NodeType -> Cardinality -> Symbol -> Relation
  Backward ::
    NodeType ->
    Cardinality ->
    Symbol ->
    Cardinality ->
    NodeType ->
    Relation
  Existence :: NodeType -> Relation
  Universal :: NodeType -> Relation

type Domain :: Relation -> NodeType
type family Domain rel where
  Domain (Directed a na name nb b) = a
  Domain (Backward b nb name na a) = b
  Domain (Symmetric nodeType n name) = nodeType
  Domain (Existence nodeType) = Universe
  Domain (Universal nodeType) = nodeType

type DomainCardinality :: Relation -> Cardinality
type family DomainCardinality rel where
  DomainCardinality (Directed a na name nb b) = na
  DomainCardinality (Backward b nb name na a) = nb
  DomainCardinality (Symmetric nodeType n name) = n
  DomainCardinality (Existence nodeType) = One
  DomainCardinality (Universal nodeType) = Many

type Codomain :: Relation -> NodeType
type family Codomain rel where
  Codomain (Directed a na name nb b) = b
  Codomain (Backward b nb name na a) = a
  Codomain (Symmetric nodeType n name) = nodeType
  Codomain (Existence nodeType) = nodeType
  Codomain (Universal nodeType) = Universe

type CodomainCardinality :: Relation -> Cardinality
type family CodomainCardinality rel where
  CodomainCardinality (Directed a na name nb b) = nb
  CodomainCardinality (Backward b nb name na a) = na
  CodomainCardinality (Symmetric nodeType n name) = n
  CodomainCardinality (Existence nodeType) = Many
  CodomainCardinality (Universal nodeType) = One

type Inverse :: Relation -> Relation
type family Inverse relation where
  Inverse (Directed a na name nb b) = Backward b nb name na a
  Inverse (Backward b nb name na a) = Directed a na name nb b
  Inverse (Symmetric nodeType n name) = Symmetric nodeType n name
  Inverse (Existence nodeType) = Universal nodeType
  Inverse (Universal nodeType) = Existence nodeType

-- | The kind for an edgy schema.  An edgy schema is itself a type, specifying
-- the node types, attributes, and relations that make up the data model.
type Schema = [SchemaDef]

-- | The kind for a single definition in an edgy schema.
data SchemaDef where
  DefNode :: NodeType -> SchemaDef
  DefAttribute :: AttributeSpec -> SchemaDef
  DefRelation :: Relation -> SchemaDef

type KnownSchema :: Schema -> Constraint
class Typeable schema => KnownSchema schema where
  foldAttributes :: Proxy schema -> AttributeFold a -> a -> a
  foldRelations :: Proxy schema -> RelationFold a -> a -> a

instance KnownSchema '[] where
  foldAttributes _ _ x = x
  foldRelations _ _ x = x

instance
  (Typeable nodeType, KnownSchema schema) =>
  KnownSchema (DefNode nodeType : schema)
  where
  foldAttributes _ f x = foldAttributes (Proxy :: Proxy schema) f x
  foldRelations _ f x = foldRelations (Proxy :: Proxy schema) f x

instance
  (Typeable relation, Typeable (Codomain relation), KnownSchema schema) =>
  KnownSchema (DefRelation relation ': schema)
  where
  foldAttributes _ f x = foldAttributes (Proxy :: Proxy schema) f x
  foldRelations _ f x =
    foldRelations (Proxy :: Proxy schema) f (f (Proxy :: Proxy relation) x)

instance
  ( Typeable attr,
    Binary (AttributeType attr),
    KnownSchema schema
  ) =>
  KnownSchema (DefAttribute attr ': schema)
  where
  foldAttributes _ f x =
    foldAttributes (Proxy :: Proxy schema) f (f (Proxy :: Proxy attr) x)
  foldRelations _ f x = foldRelations (Proxy :: Proxy schema) f x

type HasNode :: Schema -> NodeType -> Constraint
class (KnownSchema schema, Typeable nodeType) => HasNode schema nodeType

instance
  {-# OVERLAPS #-}
  (Typeable nodeType, KnownSchema rest) =>
  HasNode (DefNode nodeType : rest) nodeType

instance
  {-# OVERLAPPABLE #-}
  (KnownSchema (def : rest), HasNode rest nodeType) =>
  HasNode (def : rest) nodeType

instance
  ( Typeable nodeType,
    TypeError (Text "Node type missing from schema: " :<>: ShowType nodeType)
  ) =>
  HasNode '[] nodeType

type HasAttribute :: Schema -> NodeType -> Symbol -> AttributeSpec -> Constraint
class
  ( KnownSchema schema,
    Typeable nodeType,
    KnownSymbol name,
    Typeable attr,
    Typeable (AttributeType attr),
    Binary (AttributeType attr)
  ) =>
  HasAttribute schema nodeType name attr
    | schema nodeType name -> attr

instance
  {-# OVERLAPS #-}
  ( Typeable nodeType,
    KnownSymbol name,
    Typeable t,
    Binary t,
    KnownSchema rest
  ) =>
  HasAttribute (DefAttribute (Attribute nodeType name t) : rest) nodeType name (Attribute nodeType name t)

instance
  {-# OVERLAPPABLE #-}
  (KnownSchema (def : rest), HasAttribute rest nodeType name attr) =>
  HasAttribute (def : rest) nodeType name attr

instance
  ( Typeable nodeType,
    KnownSymbol name,
    TypeError (Text "Attribute missing from schema: " :<>: Text name :<>: Text " on " :<>: ShowType nodeType)
  ) =>
  HasAttribute '[] nodeType name (Attribute nodeType name Void)

type HasRelation :: Schema -> Relation -> Constraint
class
  ( KnownSchema schema,
    Typeable rel,
    Typeable (Domain rel),
    KnownCardinality (DomainCardinality rel),
    Typeable (Codomain rel),
    KnownCardinality (CodomainCardinality rel)
  ) =>
  HasRelation schema rel

instance
  {-# OVERLAPS #-}
  ( Typeable rel,
    Typeable (Domain rel),
    KnownCardinality (DomainCardinality rel),
    Typeable (Codomain rel),
    KnownCardinality (CodomainCardinality rel),
    KnownSchema rest
  ) =>
  HasRelation (DefRelation rel : rest) rel

instance
  {-# OVERLAPPABLE #-}
  (KnownSchema (def : rest), HasRelation rest rel) =>
  HasRelation (def : rest) rel

instance
  ( Typeable rel,
    Typeable (Domain rel),
    KnownCardinality (DomainCardinality rel),
    Typeable (Codomain rel),
    KnownCardinality (CodomainCardinality rel),
    TypeError (Text "Relation missing from schema: " :<>: ShowType rel)
  ) =>
  HasRelation '[] rel

type AttributeFold :: Type -> Type
type AttributeFold a =
  forall (attr :: AttributeSpec).
  (Typeable attr, Binary (AttributeType attr)) =>
  Proxy attr ->
  a ->
  a

type RelationFold :: Type -> Type
type RelationFold a =
  forall (relation :: Relation).
  (Typeable relation, Typeable (Codomain relation)) =>
  Proxy relation ->
  a ->
  a
