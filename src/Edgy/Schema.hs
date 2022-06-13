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
    Target,
    TargetCardinality,
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

import Data.Binary (Binary (..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.Type.Equality (testEquality, (:~:) (..))
import Data.Typeable (Typeable)
import Data.Void (Void)
import Edgy.Cardinality (Cardinality (..), KnownCardinality)
import GHC.TypeLits (ErrorMessage (..), KnownSymbol, Symbol, TypeError)
import Type.Reflection (typeRep)

-- The kind for node types.  There is exactly one node of the type 'Universe',
-- as well as any number of 'DataNode' types created by the application.
data NodeType where
  Universe :: NodeType
  DataNode :: Symbol -> NodeType

data AttributeSpec where
  (:::) :: Symbol -> Type -> AttributeSpec

type AttributeType :: AttributeSpec -> Type
type family AttributeType attr where
  AttributeType (_ ::: t) = t

data RelationSpec where
  Relation ::
    Symbol ->
    Cardinality ->
    NodeType ->
    RelationSpec

type ExistenceSpec :: Symbol -> RelationSpec
type ExistenceSpec typeName =
  Relation typeName Many (DataNode typeName)

type UniversalSpec :: Symbol -> RelationSpec
type UniversalSpec typeName =
  Relation "Universe" One Universe

type Target :: RelationSpec -> NodeType
type family Target rel where
  Target (Relation _ _ nodeType) = nodeType

type TargetCardinality :: RelationSpec -> Cardinality
type family TargetCardinality rel where
  TargetCardinality (Relation _ n _) = n

-- | The kind for an edgy schema.  An edgy schema is itself a type, specifying
-- the node types, attributes, and relations that make up the data model.
type Schema = [SchemaDef]

-- | The kind for a single definition in an edgy schema.
data SchemaDef where
  DefNode :: NodeType -> [AttributeSpec] -> SchemaDef
  DefDirected ::
    Symbol ->
    Cardinality ->
    NodeType ->
    Symbol ->
    Cardinality ->
    NodeType ->
    SchemaDef
  DefSymmetric :: Symbol -> Cardinality -> NodeType -> SchemaDef

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
    forall (nodeType :: NodeType) (a :: Type).
    Typeable nodeType =>
    Proxy schema ->
    Proxy nodeType ->
    ( forall (relation :: RelationSpec) (inverse :: RelationSpec).
      (Typeable relation, Typeable (Target relation), Typeable inverse, Typeable (Target inverse)) =>
      Proxy relation ->
      Proxy inverse ->
      a ->
      a
    ) ->
    a ->
    a

instance KnownSchema '[] where
  foldAttributes _ _ _ = id
  foldRelations _ _ _ = id

instance
  {-# OVERLAPS #-}
  (KnownSymbol typeName, KnownAttrs attrs, KnownSchema schema) =>
  KnownSchema (DefNode (DataNode typeName) attrs : schema)
  where
  foldAttributes _ (p :: Proxy fromNode) f x =
    case testEquality (typeRep @(DataNode typeName)) (typeRep @fromNode) of
      Just Refl -> foldNodeAttributes (Proxy @attrs) f x
      _ -> foldAttributes (Proxy @schema) p f x
  foldRelations _ (p :: Proxy fromNode) f x =
    let x' = case testEquality (typeRep @(DataNode typeName)) (typeRep @fromNode) of
          Just Refl -> f universal existence x
          _ -> x
        x'' = case testEquality (typeRep @Universe) (typeRep @fromNode) of
          Just Refl -> f existence universal x'
          _ -> x'
     in foldRelations (Proxy @schema) p f x''
    where
      existence = Proxy @(ExistenceSpec typeName)
      universal = Proxy @(UniversalSpec typeName)

instance
  {-# OVERLAPPABLE #-}
  (KnownAttrs attrs, KnownSchema schema) =>
  KnownSchema (DefNode Universe attrs : schema)
  where
  foldAttributes _ (p :: Proxy fromNode) f x =
    case testEquality (typeRep @Universe) (typeRep @fromNode) of
      Just Refl -> foldNodeAttributes (Proxy @attrs) f x
      _ -> foldAttributes (Proxy @schema) p f x
  foldRelations _ = foldRelations (Proxy @schema)

instance
  ( KnownSymbol fwdName,
    KnownCardinality fwdCard,
    Typeable fwdType,
    KnownSymbol bwdName,
    KnownCardinality bwdCard,
    Typeable bwdType,
    KnownSchema schema
  ) =>
  KnownSchema (DefDirected fwdName fwdCard fwdType bwdName bwdCard bwdType : schema)
  where
  foldAttributes _ p f x = foldAttributes (Proxy @schema) p f x
  foldRelations _ (p :: Proxy fromNode) f x =
    let x' = case testEquality (typeRep @bwdType) (typeRep @fromNode) of
          Just Refl -> f fwd bwd x
          _ -> x
        x'' = case testEquality (typeRep @fwdType) (typeRep @fromNode) of
          Just Refl -> f bwd fwd x'
          _ -> x'
     in foldRelations (Proxy @schema) p f x''
    where
      fwd = Proxy @(Relation fwdName fwdCard fwdType)
      bwd = Proxy @(Relation bwdName bwdCard bwdType)

instance
  ( KnownSymbol name,
    Typeable nodeType,
    KnownCardinality n,
    KnownSchema schema
  ) =>
  KnownSchema (DefSymmetric name n nodeType : schema)
  where
  foldAttributes _ p f x = foldAttributes (Proxy @schema) p f x
  foldRelations _ (p :: Proxy fromNode) f x =
    let x' = case testEquality (typeRep @nodeType) (typeRep @fromNode) of
          Just Refl -> f fwd fwd x
          _ -> x
     in foldRelations (Proxy @schema) p f x'
    where
      fwd = Proxy @(Relation name n nodeType)

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
    (name ::: t : rest)
    name
    (name ::: t)

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
  NodeHasAttribute nodeType '[] name (name ::: Void)

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
  HasAttribute '[] nodeType name (name ::: Void)

type HasRelation ::
  Schema ->
  NodeType ->
  Symbol ->
  RelationSpec ->
  RelationSpec ->
  Constraint
class
  ( KnownSchema schema,
    KnownSymbol name,
    Typeable nodeType,
    Typeable spec,
    Typeable (Target spec),
    KnownCardinality (TargetCardinality spec),
    Typeable inverse,
    Target inverse ~ nodeType,
    KnownCardinality (TargetCardinality inverse)
  ) =>
  HasRelation schema nodeType name spec inverse
    | schema nodeType name -> spec,
      schema nodeType name -> inverse

instance
  {-# OVERLAPS #-}
  ( KnownSymbol typeName,
    KnownAttrs attrs,
    KnownSchema rest
  ) =>
  HasRelation
    (DefNode (DataNode typeName) attrs : rest)
    Universe
    typeName
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
    (DataNode typeName)
    "Universe"
    (UniversalSpec typeName)
    (ExistenceSpec typeName)

instance
  {-# OVERLAPS #-}
  ( KnownSymbol fwdName,
    KnownCardinality fwdCard,
    Typeable fwdType,
    KnownSymbol bwdName,
    KnownCardinality bwdCard,
    Typeable bwdType,
    KnownSchema rest
  ) =>
  HasRelation
    (DefDirected fwdName fwdCard fwdType bwdName bwdCard bwdType : rest)
    bwdType
    fwdName
    (Relation fwdName fwdCard fwdType)
    (Relation bwdName bwdCard bwdType)

instance
  {-# OVERLAPS #-}
  ( KnownSymbol fwdName,
    KnownCardinality fwdCard,
    Typeable fwdType,
    KnownSymbol bwdName,
    KnownCardinality bwdCard,
    Typeable bwdType,
    KnownSchema rest
  ) =>
  HasRelation
    (DefDirected fwdName fwdCard fwdType bwdName bwdCard bwdType : rest)
    fwdType
    bwdName
    (Relation bwdName bwdCard bwdType)
    (Relation fwdName fwdCard fwdType)

instance
  {-# OVERLAPS #-}
  ( KnownSymbol name,
    Typeable nodeType,
    KnownCardinality n,
    KnownSchema rest
  ) =>
  HasRelation
    (DefSymmetric name n nodeType : rest)
    nodeType
    name
    (Relation name n nodeType)
    (Relation name n nodeType)

instance
  {-# OVERLAPPABLE #-}
  (KnownSchema (def : rest), HasRelation rest nodeType name spec inverse) =>
  HasRelation (def : rest) nodeType name spec inverse

instance
  ( KnownSymbol relation,
    Typeable nodeType,
    TypeError (Text "Relation missing from schema: " :<>: Text relation :<>: Text " on " :<>: ShowType nodeType)
  ) =>
  HasRelation
    '[]
    nodeType
    relation
    (Relation relation One Universe)
    (Relation relation One nodeType)
