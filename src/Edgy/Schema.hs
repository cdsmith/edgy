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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Edgy.Schema
  ( -- * Nodes
    NodeType (..),

    -- * Attributes
    AttributeSpec (..),
    AttributeType,

    -- * Relations
    RelationSpec (..),
    RelationId (..),
    Domain,
    DomainCardinality,
    Codomain,
    CodomainCardinality,
    ExistenceSpec,
    UniversalSpec,

    -- * Schema
    Schema,
    SchemaDef (..),
    KnownSchema (..),
    HasNode,
    HasRelation,
    HasAttribute,
  )
where

import Edgy.Cardinality (Cardinality (..), KnownCardinality)
import Data.Binary (Binary (..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.Type.Equality (testEquality, (:~:) (..))
import Data.Typeable (Typeable)
import Data.Void (Void)
import GHC.TypeLits (ErrorMessage (..), KnownSymbol, Symbol, TypeError)
import Type.Reflection (typeRep)

-- The kind for node types.  There is exactly one node of the type 'Universe',
-- as well as any number of 'DataNode' types created by the application.
data NodeType where
  Universe :: NodeType
  DataNode :: Symbol -> NodeType

data AttributeSpec where
  Attribute :: Symbol -> Type -> AttributeSpec

type AttributeType :: AttributeSpec -> Type
type family AttributeType attr where
  AttributeType (Attribute _ t) = t

data RelationId where
  Explicit :: Symbol -> RelationId
  Inverse :: Symbol -> RelationId
  Existence :: Symbol -> RelationId
  Universal :: Symbol -> RelationId

data RelationSpec where
  Relation ::
    RelationId ->
    NodeType ->
    Cardinality ->
    NodeType ->
    Cardinality ->
    RelationSpec

type ExistenceSpec :: Symbol -> RelationSpec
type ExistenceSpec typeName =
  Relation (Existence typeName) Universe One (DataNode typeName) Many

type UniversalSpec :: Symbol -> RelationSpec
type UniversalSpec typeName =
  Relation (Universal typeName) (DataNode typeName) Many Universe One

type Domain :: RelationSpec -> NodeType
type family Domain rel where
  Domain (Relation _ nodeType _ _ _) = nodeType

type DomainCardinality :: RelationSpec -> Cardinality
type family DomainCardinality rel where
  DomainCardinality (Relation _ _ n _ _) = n

type Codomain :: RelationSpec -> NodeType
type family Codomain rel where
  Codomain (Relation _ _ _ nodeType _) = nodeType

type CodomainCardinality :: RelationSpec -> Cardinality
type family CodomainCardinality rel where
  CodomainCardinality (Relation _ _ _ _ n) = n

-- | The kind for an edgy schema.  An edgy schema is itself a type, specifying
-- the node types, attributes, and relations that make up the data model.
type Schema = [SchemaDef]

-- | The kind for a single definition in an edgy schema.
data SchemaDef where
  DefNode :: NodeType -> [AttributeSpec] -> SchemaDef
  DefDirected ::
    Cardinality ->
    NodeType ->
    Symbol ->
    Cardinality ->
    NodeType ->
    SchemaDef
  DefSymmetric :: NodeType -> Symbol -> Cardinality -> SchemaDef

type KnownAttrs :: [AttributeSpec] -> Constraint
class Typeable attrs => KnownAttrs attrs where
  foldNodeAttributes ::
    Proxy attrs ->
    ( forall (attr :: AttributeSpec).
      (Typeable attr, Binary (AttributeType attr)) =>
      Proxy attr ->
      a ->
      a
    ) ->
    a ->
    a

instance KnownAttrs '[] where
  foldNodeAttributes _ _ = id

instance
  (Typeable attr, Binary (AttributeType attr), KnownAttrs attrs) =>
  KnownAttrs (attr : attrs)
  where
  foldNodeAttributes _ f x =
    foldNodeAttributes (Proxy @attrs) f (f (Proxy @attr) x)

type KnownSchema :: Schema -> Constraint
class Typeable schema => KnownSchema schema where
  foldAttributes ::
    forall (nodeType :: NodeType) (a :: Type).
    Typeable nodeType =>
    Proxy schema ->
    Proxy nodeType ->
    ( forall (attr :: AttributeSpec).
      (Typeable attr, Binary (AttributeType attr)) =>
      Proxy attr ->
      a ->
      a
    ) ->
    a ->
    a
  foldRelations ::
    Proxy schema ->
    ( forall (relation :: RelationSpec) (inverse :: RelationSpec).
      ( Typeable relation,
        Typeable (Domain relation),
        Typeable (Codomain relation),
        Typeable inverse,
        Domain inverse ~ Codomain relation,
        Codomain inverse ~ Domain relation
      ) =>
      Proxy relation ->
      Proxy inverse ->
      a ->
      a
    ) ->
    a ->
    a

instance KnownSchema '[] where
  foldAttributes _ _ _ = id
  foldRelations _ _ = id

instance
  {-# OVERLAPS #-}
  (KnownSymbol typeName, KnownAttrs attrs, KnownSchema schema) =>
  KnownSchema (DefNode (DataNode typeName) attrs : schema)
  where
  foldAttributes _ (p :: Proxy targetNode) f x =
    case testEquality (typeRep @(DataNode typeName)) (typeRep @targetNode) of
      Just Refl -> foldNodeAttributes (Proxy @attrs) f x
      _ -> foldAttributes (Proxy @schema) p f x
  foldRelations _ f x =
    foldRelations (Proxy @schema) f (f existence universal (f universal existence x))
    where
      existence = Proxy @(ExistenceSpec typeName)
      universal = Proxy @(UniversalSpec typeName)

instance
  {-# OVERLAPPABLE #-}
  (KnownAttrs attrs, KnownSchema schema) =>
  KnownSchema (DefNode Universe attrs : schema)
  where
  foldAttributes _ (p :: Proxy targetNode) f x =
    case testEquality (typeRep @Universe) (typeRep @targetNode) of
      Just Refl -> foldNodeAttributes (Proxy @attrs) f x
      _ -> foldAttributes (Proxy @schema) p f x
  foldRelations _ = foldRelations (Proxy @schema)

instance
  ( KnownSymbol name,
    Typeable a,
    KnownCardinality na,
    Typeable b,
    KnownCardinality nb,
    KnownSchema schema
  ) =>
  KnownSchema (DefDirected na a name nb b : schema)
  where
  foldAttributes _ p f x = foldAttributes (Proxy @schema) p f x
  foldRelations _ f x =
    foldRelations (Proxy @schema) f (f fwd bwd (f bwd fwd x))
    where
      fwd = Proxy @(Relation (Explicit name) a na b nb)
      bwd = Proxy @(Relation (Inverse name) b nb a na)

instance
  ( KnownSymbol name,
    Typeable nodeType,
    KnownCardinality n,
    KnownSchema schema
  ) =>
  KnownSchema (DefSymmetric nodeType name n : schema)
  where
  foldAttributes _ p f x = foldAttributes (Proxy @schema) p f x
  foldRelations _ f x =
    foldRelations (Proxy @schema) f (f fwd fwd x)
    where
      fwd = Proxy @(Relation (Explicit name) nodeType n nodeType n)

type HasNode :: Schema -> NodeType -> Constraint
class (KnownSchema schema, Typeable nodeType) => HasNode schema nodeType

instance
  {-# OVERLAPS #-}
  (KnownSchema (DefNode nodeType attrs : rest), Typeable nodeType, KnownAttrs attrs) =>
  HasNode (DefNode nodeType attrs : rest) nodeType

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

type NodeHasAttribute ::
  NodeType -> [AttributeSpec] -> Symbol -> AttributeSpec -> Constraint
class
  NodeHasAttribute nodeType attrs name attr
    | attrs name -> attr,
      attr -> name

instance
  {-# OVERLAPS #-}
  NodeHasAttribute
    nodeType
    (Attribute name t : rest)
    name
    (Attribute name t)

instance
  {-# OVERLAPPABLE #-}
  NodeHasAttribute nodeType rest name attr =>
  NodeHasAttribute nodeType (other : rest) name attr

instance
  ( TypeError
      ( Text "Attribute missing from schema: "
          :<>: Text name
          :<>: Text " on "
          :<>: ShowType nodeType
      )
  ) =>
  NodeHasAttribute nodeType '[] name (Attribute name Void)

instance
  {-# OVERLAPS #-}
  ( KnownSchema (DefNode nodeType attrs : rest),
    Typeable nodeType,
    KnownSymbol name,
    NodeHasAttribute nodeType attrs name attr,
    Typeable attr,
    Typeable (AttributeType attr),
    Binary (AttributeType attr)
  ) =>
  HasAttribute
    (DefNode nodeType attrs : rest)
    nodeType
    name
    attr

instance
  {-# OVERLAPPABLE #-}
  (KnownSchema (def : rest), HasAttribute rest nodeType name attr) =>
  HasAttribute (def : rest) nodeType name attr

instance
  ( Typeable nodeType,
    KnownSymbol name,
    TypeError
      ( Text "Attribute missing from schema: "
          :<>: Text name
          :<>: Text " on "
          :<>: ShowType nodeType
      )
  ) =>
  HasAttribute '[] nodeType name (Attribute name Void)

type HasRelation ::
  Schema ->
  RelationId ->
  RelationSpec ->
  RelationSpec ->
  Constraint
class
  ( KnownSchema schema,
    Typeable relation,
    Typeable spec,
    Typeable (Domain spec),
    KnownCardinality (DomainCardinality spec),
    Typeable (Codomain spec),
    KnownCardinality (CodomainCardinality spec),
    Typeable inverse,
    Domain inverse ~ Codomain spec,
    DomainCardinality inverse ~ CodomainCardinality spec,
    Codomain inverse ~ Domain spec,
    CodomainCardinality inverse ~ DomainCardinality spec
  ) =>
  HasRelation schema relation spec inverse
    | schema relation -> spec,
      schema relation -> inverse,
      spec -> relation

instance
  {-# OVERLAPS #-}
  ( KnownSymbol typeName,
    KnownAttrs attrs,
    KnownSchema rest
  ) =>
  HasRelation
    (DefNode (DataNode typeName) attrs : rest)
    (Existence typeName)
    (ExistenceSpec typeName)
    (UniversalSpec typeName)

instance
  {-# OVERLAPS #-}
  ( KnownSymbol typeName,
    KnownAttrs attrs,
    KnownSchema rest
  ) =>
  HasRelation
    (DefNode (DataNode typeName) attrs : rest)
    (Universal typeName)
    (UniversalSpec typeName)
    (ExistenceSpec typeName)

instance
  {-# OVERLAPS #-}
  ( KnownSymbol name,
    Typeable a,
    KnownCardinality na,
    Typeable b,
    KnownCardinality nb,
    KnownSchema rest
  ) =>
  HasRelation
    (DefDirected na a name nb b : rest)
    (Explicit name)
    (Relation (Explicit name) a na b nb)
    (Relation (Inverse name) b nb a na)

instance
  {-# OVERLAPS #-}
  ( KnownSymbol name,
    Typeable a,
    KnownCardinality na,
    Typeable b,
    KnownCardinality nb,
    KnownSchema rest
  ) =>
  HasRelation
    (DefDirected na a name nb b : rest)
    (Inverse name)
    (Relation (Inverse name) b nb a na)
    (Relation (Explicit name) a na b nb)

instance
  {-# OVERLAPS #-}
  ( KnownSymbol name,
    Typeable nodeType,
    KnownCardinality n,
    KnownSchema rest
  ) =>
  HasRelation
    (DefSymmetric nodeType name n : rest)
    (Explicit name)
    (Relation (Explicit name) nodeType n nodeType n)
    (Relation (Explicit name) nodeType n nodeType n)

instance
  {-# OVERLAPPABLE #-}
  (KnownSchema (def : rest), HasRelation rest relation spec inverse) =>
  HasRelation (def : rest) relation spec inverse

instance
  ( Typeable relation,
    TypeError (Text "Relation missing from schema: " :<>: ShowType relation)
  ) =>
  HasRelation
    '[]
    relation
    (Relation relation Universe One Universe One)
    (Relation relation Universe One Universe One)
