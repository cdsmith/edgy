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
{-# LANGUAGE TypeApplications #-}

module Schema
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

    -- * Schema
    Schema,
    SchemaDef (..),
    KnownSchema (..),
    HasNode,
    HasRelation,
    HasAttribute,
  )
where

import Cardinality (Cardinality (..), KnownCardinality)
import Data.Binary (Binary (..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.Typeable (Typeable)
import Data.Void (Void)
import GHC.TypeLits (ErrorMessage (..), KnownSymbol, Symbol, TypeError)
import Data.Type.Equality ((:~:)(..), testEquality)
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
  Existence :: NodeType -> RelationId
  Universal :: NodeType -> RelationId

data RelationSpec where
  Relation ::
    RelationId ->
    NodeType ->
    Cardinality ->
    NodeType ->
    Cardinality ->
    RelationSpec

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
    Symbol ->
    NodeType ->
    Cardinality ->
    NodeType ->
    Cardinality ->
    SchemaDef
  DefSymmetric :: Symbol -> NodeType -> Cardinality -> SchemaDef

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
    ( forall (relation :: RelationSpec).
      (Typeable relation, Typeable (Codomain relation)) =>
      Proxy relation ->
      a ->
      a
    ) ->
    a ->
    a

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

instance KnownSchema '[] where
  foldAttributes _ _ _ = id
  foldRelations _ _ = id

instance
  (Typeable nodeType, KnownAttrs attrs, KnownSchema schema) =>
  KnownSchema (DefNode nodeType attrs : schema)
  where
  foldAttributes _ (p :: Proxy targetNode) f x =
    case testEquality (typeRep @nodeType) (typeRep @targetNode) of
      Just Refl -> foldNodeAttributes (Proxy @attrs) f x
      _ -> foldAttributes (Proxy @schema) p f x
  foldRelations _ f x =
    foldRelations (Proxy @schema) f (f existence (f universal x))
    where
      existence =
        Proxy ::
          Proxy
            (Relation (Existence nodeType) Universe One nodeType Many)
      universal =
        Proxy ::
          Proxy
            (Relation (Universal nodeType) nodeType Many Universe One)

instance
  ( KnownSymbol name,
    Typeable a,
    KnownCardinality na,
    Typeable b,
    KnownCardinality nb,
    KnownSchema schema
  ) =>
  KnownSchema (DefDirected name a na b nb : schema)
  where
  foldAttributes _ p f x = foldAttributes (Proxy @schema) p f x
  foldRelations _ f x =
    foldRelations (Proxy @schema) f (f fwd (f bwd x))
    where
      fwd = Proxy @(Relation (Explicit name) a na b nb)
      bwd = Proxy @(Relation (Inverse name) b nb a na)

instance
  ( KnownSymbol name,
    Typeable nodeType,
    KnownCardinality n,
    KnownSchema schema
  ) =>
  KnownSchema (DefSymmetric name nodeType n : schema)
  where
  foldAttributes _ p f x = foldAttributes (Proxy @schema) p f x
  foldRelations _ f x =
    foldRelations (Proxy @schema) f (f fwd x)
    where
      fwd = Proxy @(Relation (Explicit name) nodeType n nodeType n)

type HasNode :: Schema -> NodeType -> Constraint
class (KnownSchema schema, Typeable nodeType) => HasNode schema nodeType

instance
  {-# OVERLAPS #-}
  (Typeable nodeType, KnownAttrs attrs, KnownSchema rest) =>
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
class NodeHasAttribute nodeType attrs name attr | attrs name -> attr

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
  ( Typeable nodeType,
    KnownAttrs attrs,
    KnownSymbol name,
    NodeHasAttribute nodeType attrs name attr,
    Typeable attr,
    Typeable (AttributeType attr),
    Binary (AttributeType attr),
    KnownSchema rest
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

type HasRelation :: Schema -> RelationId -> RelationSpec -> Constraint
class
  ( KnownSchema schema,
    Typeable relation,
    Typeable spec,
    Typeable (Domain spec),
    KnownCardinality (DomainCardinality spec),
    Typeable (Codomain spec),
    KnownCardinality (CodomainCardinality spec)
  ) =>
  HasRelation schema relation spec
    | schema relation -> spec

instance
  {-# OVERLAPS #-}
  ( Typeable nodeType,
    KnownAttrs attrs,
    KnownSchema rest
  ) =>
  HasRelation
    (DefNode nodeType attrs : rest)
    (Existence nodeType)
    (Relation (Existence nodeType) Universe One nodeType Many)

instance
  {-# OVERLAPS #-}
  ( Typeable nodeType,
    KnownAttrs attrs,
    KnownSchema rest
  ) =>
  HasRelation
    (DefNode nodeType attrs : rest)
    (Universal nodeType)
    (Relation (Universal nodeType) nodeType Many Universe One)

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
    (DefDirected name a na b nb : rest)
    (Explicit name)
    (Relation (Explicit name) a na b nb)

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
    (DefDirected name a na b nb : rest)
    (Inverse name)
    (Relation (Inverse name) b nb a na)

instance
  {-# OVERLAPS #-}
  ( KnownSymbol name,
    Typeable nodeType,
    KnownCardinality n,
    KnownSchema rest
  ) =>
  HasRelation
    (DefSymmetric name nodeType n : rest)
    (Explicit name)
    (Relation (Explicit name) nodeType n nodeType n)

instance
  {-# OVERLAPPABLE #-}
  (KnownSchema (def : rest), HasRelation rest relation spec) =>
  HasRelation (def : rest) relation spec

instance
  ( Typeable relation,
    TypeError (Text "Relation missing from schema: " :<>: ShowType relation)
  ) =>
  HasRelation '[] relation (Relation relation Universe One Universe One)
