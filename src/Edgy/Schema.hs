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

module Edgy.Schema where

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

type RelationName :: RelationSpec -> Symbol
type family RelationName relation where
  RelationName (Relation s _ _) = s

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
      ( Typeable relation,
        KnownSymbol (RelationName relation),
        Typeable (Target relation),
        Typeable inverse,
        KnownSymbol (RelationName inverse),
        Typeable (Target inverse)
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
  (KnownSchema schema, Typeable nodeType, NodeLookup schema nodeType) =>
  HasNode schema nodeType

type NodeLookup :: Schema -> NodeType -> Constraint
class NodeLookup schema nodeType

instance {-# OVERLAPS #-} NodeLookup (DefNode nodeType attrs : rest) nodeType

instance
  {-# OVERLAPPABLE #-}
  NodeLookup rest nodeType =>
  NodeLookup (def : rest) nodeType

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
  ( KnownSchema schema,
    Typeable nodeType,
    KnownSymbol name,
    Typeable attr,
    Typeable (AttributeType attr),
    Binary (AttributeType attr),
    AttributeLookup schema nodeType name attr
  ) =>
  HasAttribute schema nodeType name attr

type NodeAttributeLookup ::
  NodeType -> [AttributeSpec] -> Symbol -> AttributeSpec -> Constraint
class
  NodeAttributeLookup nodeType attrs name attr
    | attrs name -> attr,
      attr -> name

instance
  {-# OVERLAPS #-}
  NodeAttributeLookup
    nodeType
    (name ::: t : rest)
    name
    (name ::: t)

instance
  {-# OVERLAPPABLE #-}
  NodeAttributeLookup nodeType rest name attr =>
  NodeAttributeLookup nodeType (other : rest) name attr

instance
  ( TypeError
      ( Text "Attribute missing from schema: "
          :<>: Text name
          :<>: Text " on "
          :<>: ShowType nodeType
      )
  ) =>
  NodeAttributeLookup nodeType '[] name (name ::: Void)

type AttributeLookup ::
  Schema -> NodeType -> Symbol -> AttributeSpec -> Constraint
class
  AttributeLookup schema nodeType name attr
    | schema nodeType name -> attr,
      attr -> name

instance
  {-# OVERLAPS #-}
  NodeAttributeLookup nodeType attrs name attr =>
  AttributeLookup (DefNode nodeType attrs : rest) nodeType name attr

instance
  {-# OVERLAPPABLE #-}
  AttributeLookup rest nodeType name attr =>
  AttributeLookup (def : rest) nodeType name attr

instance
  ( TypeError
      ( Text "Attribute missing from schema: "
          :<>: Text name
          :<>: Text " on "
          :<>: ShowType nodeType
      )
  ) =>
  AttributeLookup '[] nodeType name (name ::: Void)

data Mutability = Mutable | Immutable

type HasRelation ::
  Schema ->
  NodeType ->
  Symbol ->
  RelationSpec ->
  RelationSpec ->
  Mutability ->
  Constraint
class
  ( KnownSchema schema,
    KnownSymbol name,
    Typeable nodeType,
    Typeable spec,
    KnownSymbol (RelationName spec),
    Typeable (Target spec),
    KnownCardinality (TargetCardinality spec),
    Typeable inverse,
    KnownSymbol (RelationName inverse),
    Target inverse ~ nodeType,
    KnownCardinality (TargetCardinality inverse)
  ) =>
  HasRelation schema nodeType name spec inverse mutable
    | schema nodeType name -> spec inverse mutable

instance
  ( KnownSchema schema,
    KnownSymbol name,
    Typeable nodeType,
    Typeable spec,
    KnownSymbol (RelationName spec),
    Typeable (Target spec),
    KnownCardinality (TargetCardinality spec),
    Typeable inverse,
    KnownSymbol (RelationName inverse),
    Target inverse ~ nodeType,
    KnownCardinality (TargetCardinality inverse),
    RelationLookup schema nodeType name spec inverse mutable
  ) =>
  HasRelation schema nodeType name spec inverse mutable

type RelationLookup ::
  Schema ->
  NodeType ->
  Symbol ->
  RelationSpec ->
  RelationSpec ->
  Mutability ->
  Constraint
class
  RelationLookup schema nodeType name spec inverse mutable
    | schema nodeType name -> spec inverse mutable

instance
  {-# OVERLAPS #-}
  (mutability ~ Immutable) =>
  RelationLookup
    (DefNode (DataNode typeName) attrs : rest)
    Universe
    typeName
    (ExistenceSpec typeName)
    (UniversalSpec typeName)
    mutability

instance
  {-# OVERLAPS #-}
  (mutability ~ Immutable) =>
  RelationLookup
    (DefNode (DataNode typeName) attrs : rest)
    (DataNode typeName)
    "Universe"
    (UniversalSpec typeName)
    (ExistenceSpec typeName)
    mutability

instance
  {-# OVERLAPS #-}
  (mutability ~ Mutable) =>
  RelationLookup
    (DefDirected fwdName fwdCard fwdType bwdName bwdCard bwdType : rest)
    bwdType
    fwdName
    (Relation fwdName fwdCard fwdType)
    (Relation bwdName bwdCard bwdType)
    mutability

instance
  {-# OVERLAPS #-}
  (mutability ~ Mutable) =>
  RelationLookup
    (DefDirected fwdName fwdCard fwdType bwdName bwdCard bwdType : rest)
    fwdType
    bwdName
    (Relation bwdName bwdCard bwdType)
    (Relation fwdName fwdCard fwdType)
    mutability

instance
  {-# OVERLAPS #-}
  (mutability ~ Mutable) =>
  RelationLookup
    (DefSymmetric name n nodeType : rest)
    nodeType
    name
    (Relation name n nodeType)
    (Relation name n nodeType)
    mutability

instance
  {-# OVERLAPPABLE #-}
  RelationLookup rest nodeType name spec inverse mutability =>
  RelationLookup (def : rest) nodeType name spec inverse mutability

instance
  ( TypeError
      ( Text "Relation missing from schema: "
          :<>: Text relation
          :<>: Text " on "
          :<>: ShowType nodeType
      )
  ) =>
  RelationLookup
    '[]
    nodeType
    relation
    (Relation relation One Universe)
    (Relation relation One nodeType)
    Immutable
