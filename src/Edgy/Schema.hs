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
  (::?) :: Symbol -> Type -> AttributeSpec

type family AttributeName (attr :: AttributeSpec) :: Symbol where
  AttributeName (n ::: _) = n
  AttributeName (n ::? _) = n

type family AttributeType (attr :: AttributeSpec) :: Type where
  AttributeType (_ ::: t) = t
  AttributeType (_ ::? t) = t

data RelationSpec where
  Relation ::
    Symbol ->
    Cardinality ->
    NodeType ->
    RelationSpec

type family RelationName (relation :: RelationSpec) :: Symbol where
  RelationName (Relation s _ _) = s

type ExistenceSpec (typeName :: Symbol) =
  Relation typeName Many (DataNode typeName)

type UniversalSpec (typeName :: Symbol) =
  Relation "Universe" One Universe

type family Target (rel :: RelationSpec) where
  Target (Relation _ _ nodeType) = nodeType

type family TargetCardinality (rel :: RelationSpec) where
  TargetCardinality (Relation _ n _) = n

-- | The kind for an edgy schema.  An edgy schema is itself a type, specifying
-- the node types, attributes, and relations that make up the data model.
type Schema = [SchemaDef]

-- | The kind for a single definition in an edgy schema.
data SchemaDef where
  DefNode :: NodeType -> [AttributeSpec] -> SchemaDef
  DefDirected :: RelationSpec -> RelationSpec -> SchemaDef
  DefSymmetric :: RelationSpec -> SchemaDef

class Typeable attrs => KnownAttrs nodeType attrs where
  foldNodeAttributes ::
    Proxy nodeType ->
    Proxy attrs ->
    ( forall (attr :: AttributeSpec).
      ( Typeable attr,
        KnownSymbol (AttributeName attr),
        Typeable (AttributeType attr),
        Binary (AttributeType attr)
      ) =>
      Proxy attr ->
      a ->
      a
    ) ->
    a ->
    a

  foldConstructor ::
    Proxy nodeType ->
    Proxy attrs ->
    ( forall (attr :: AttributeSpec).
      ( Typeable attr,
        KnownSymbol (AttributeName attr),
        Typeable (AttributeType attr),
        Binary (AttributeType attr)
      ) =>
      Proxy attr ->
      AttributeType attr ->
      a ->
      a
    ) ->
    a ->
    Constructor attrs a

  mapConstructor ::
    Proxy nodeType ->
    Proxy attrs ->
    (a -> b) ->
    Constructor attrs a ->
    Constructor attrs b

instance KnownAttrs nodeType '[] where
  foldNodeAttributes _ _ _ = id
  foldConstructor _ _ _ = id
  mapConstructor _ _ f = f

type family
  DupAttrCheck
    (nodeType :: NodeType)
    (attrs :: [AttributeSpec])
    (dupName :: Symbol) ::
    Constraint
  where
  DupAttrCheck nodeType ((name ::: _) : attrs) name =
    TypeError
      ( Text "Duplicate attribute: "
          :<>: Text name
          :<>: Text ", in node type "
          :<>: ShowType nodeType
      )
  DupAttrCheck nodeType ((name ::? _) : attrs) name =
    TypeError
      ( Text "Duplicate attribute: "
          :<>: Text name
          :<>: Text ", in node type "
          :<>: ShowType nodeType
      )
  DupAttrCheck nodeType (_ : attrs) name = DupAttrCheck nodeType attrs name
  DupAttrCheck nodeType '[] name = ()

instance
  ( KnownSymbol name,
    Typeable t,
    Binary t,
    KnownAttrs nodeType attrs,
    DupAttrCheck nodeType attrs name
  ) =>
  KnownAttrs nodeType ((name ::: t) : attrs)
  where
  foldNodeAttributes pType _ f x =
    foldNodeAttributes pType (Proxy @attrs) f (f (Proxy @(name ::: t)) x)
  foldConstructor pType _ f x v =
    foldConstructor
      pType
      (Proxy @attrs)
      f
      (f (Proxy @(name ::: t)) v x)
  mapConstructor pType _ f = fmap (mapConstructor pType (Proxy @attrs) f)

instance
  ( KnownSymbol name,
    Typeable t,
    Binary t,
    Monoid t,
    KnownAttrs nodeType attrs,
    DupAttrCheck nodeType attrs name
  ) =>
  KnownAttrs nodeType ((name ::? t) : attrs)
  where
  foldNodeAttributes pType _ f x =
    foldNodeAttributes pType (Proxy @attrs) f (f (Proxy @(name ::? t)) x)
  foldConstructor pType _ = foldConstructor pType (Proxy @attrs)
  mapConstructor pType _ f = mapConstructor pType (Proxy @attrs) f

class Typeable schema => KnownSchema (schema :: Schema) where
  foldAttributes ::
    forall (nodeType :: NodeType) (a :: Type).
    Typeable nodeType =>
    Proxy schema ->
    Proxy nodeType ->
    ( forall (attr :: AttributeSpec).
      ( Typeable attr,
        KnownSymbol (AttributeName attr),
        Typeable (AttributeType attr),
        Binary (AttributeType attr)
      ) =>
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
  ( KnownSymbol typeName,
    KnownAttrs (DataNode typeName) attrs,
    KnownSchema schema
  ) =>
  KnownSchema (DefNode (DataNode typeName) attrs : schema)
  where
  foldAttributes _ (p :: Proxy fromNode) f x =
    case testEquality (typeRep @(DataNode typeName)) (typeRep @fromNode) of
      Just Refl -> foldNodeAttributes p (Proxy @attrs) f x
      _ -> foldAttributes (Proxy @schema) p f x
  foldRelations _ (p :: Proxy fromNode) f x =
    let x' = case testEquality
          (typeRep @(DataNode typeName))
          (typeRep @fromNode) of
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
  (KnownAttrs Universe attrs, KnownSchema schema) =>
  KnownSchema (DefNode Universe attrs : schema)
  where
  foldAttributes _ (p :: Proxy fromNode) f x =
    case testEquality (typeRep @Universe) (typeRep @fromNode) of
      Just Refl -> foldNodeAttributes p (Proxy @attrs) f x
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
  KnownSchema
    ( DefDirected
        (Relation fwdName fwdCard fwdType)
        (Relation bwdName bwdCard bwdType)
        : schema
    )
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
  KnownSchema (DefSymmetric (Relation name n nodeType) : schema)
  where
  foldAttributes _ p f x = foldAttributes (Proxy @schema) p f x
  foldRelations _ (p :: Proxy fromNode) f x =
    let x' = case testEquality (typeRep @nodeType) (typeRep @fromNode) of
          Just Refl -> f fwd fwd x
          _ -> x
     in foldRelations (Proxy @schema) p f x'
    where
      fwd = Proxy @(Relation name n nodeType)

type family Constructor (attrs :: [AttributeSpec]) t where
  Constructor ((_ ::: param) : attrs) t = param -> Constructor attrs t
  Constructor (_ : attrs) t = Constructor attrs t
  Constructor '[] t = t

class
  (KnownSchema schema, Typeable nodeType, KnownAttrs nodeType attrs) =>
  HasNode schema nodeType attrs
    | schema nodeType -> attrs

instance
  ( KnownSchema schema,
    Typeable nodeType,
    KnownAttrs nodeType attrs,
    NodeLookup schema nodeType attrs
  ) =>
  HasNode schema nodeType attrs

class NodeLookup schema nodeType attrs | schema nodeType -> attrs

instance
  {-# OVERLAPS #-}
  NodeLookup
    (DefNode nodeType attrs : rest)
    nodeType
    attrs

instance
  {-# OVERLAPPABLE #-}
  NodeLookup rest nodeType attrs =>
  NodeLookup (def : rest) nodeType attrs

instance
  ( Typeable nodeType,
    TypeError (Text "Node type missing from schema: " :<>: ShowType nodeType)
  ) =>
  HasNode '[] nodeType '[]

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
  where
  attributeDefault ::
    Proxy schema ->
    Proxy nodeType ->
    Proxy name ->
    Maybe (AttributeType attr)

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
  where
  attributeDefault = attributeLookupDefault

class
  NodeAttributeLookup nodeType attrs name attr
    | attrs name -> attr,
      attr -> name
  where
  nodeAttributeLookupDefault ::
    Proxy nodeType ->
    Proxy attrs ->
    Proxy name ->
    Maybe (AttributeType attr)

instance
  {-# OVERLAPS #-}
  NodeAttributeLookup
    nodeType
    (name ::: t : rest)
    name
    (name ::: t)
  where
  nodeAttributeLookupDefault _ _ _ = Nothing

instance
  {-# OVERLAPS #-}
  Monoid t =>
  NodeAttributeLookup
    nodeType
    (name ::? t : rest)
    name
    (name ::? t)
  where
  nodeAttributeLookupDefault _ _ _ = Just mempty

instance
  {-# OVERLAPPABLE #-}
  NodeAttributeLookup nodeType rest name attr =>
  NodeAttributeLookup nodeType (other : rest) name attr
  where
  nodeAttributeLookupDefault pNodeType _ pName =
    nodeAttributeLookupDefault pNodeType (Proxy @rest) pName

instance
  ( TypeError
      ( Text "Attribute missing from schema: "
          :<>: Text name
          :<>: Text " on "
          :<>: ShowType nodeType
      )
  ) =>
  NodeAttributeLookup nodeType '[] name (name ::: Void)
  where
  nodeAttributeLookupDefault = undefined

class
  AttributeLookup schema nodeType name attr
    | schema nodeType name -> attr,
      attr -> name
  where
  attributeLookupDefault ::
    Proxy schema ->
    Proxy nodeType ->
    Proxy name ->
    Maybe (AttributeType attr)

instance
  {-# OVERLAPS #-}
  NodeAttributeLookup nodeType attrs name attr =>
  AttributeLookup (DefNode nodeType attrs : rest) nodeType name attr
  where
  attributeLookupDefault _ pNodeType pName =
    nodeAttributeLookupDefault pNodeType (Proxy @attrs) pName

instance
  {-# OVERLAPPABLE #-}
  AttributeLookup rest nodeType name attr =>
  AttributeLookup (def : rest) nodeType name attr
  where
  attributeLookupDefault _ pNodeType pName =
    attributeLookupDefault (Proxy @rest) pNodeType pName

instance
  TypeError (Text "Node type missing from schema: " :<>: ShowType nodeType) =>
  AttributeLookup '[] nodeType name (name ::: Void)
  where
  attributeLookupDefault = undefined

data Mutability = Mutable | Immutable

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
    ( DefDirected
        (Relation fwdName fwdCard fwdType)
        (Relation bwdName bwdCard bwdType)
        : rest
    )
    bwdType
    fwdName
    (Relation fwdName fwdCard fwdType)
    (Relation bwdName bwdCard bwdType)
    mutability

instance
  {-# OVERLAPS #-}
  (mutability ~ Mutable) =>
  RelationLookup
    ( DefDirected
        (Relation fwdName fwdCard fwdType)
        (Relation bwdName bwdCard bwdType)
        : rest
    )
    fwdType
    bwdName
    (Relation bwdName bwdCard bwdType)
    (Relation fwdName fwdCard fwdType)
    mutability

instance
  {-# OVERLAPS #-}
  (mutability ~ Mutable) =>
  RelationLookup
    (DefSymmetric (Relation name n nodeType) : rest)
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

data SchemaValidator schema where
  ValidateSchema :: KnownSchema schema => SchemaValidator schema
