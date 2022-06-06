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
    NodeType (..),
    Relation (..),
    Related (..),
    Field (..),
    Describes (..),
    Node,
  )
where

import Cardinality (Cardinality (..), Numerous)
import Control.Concurrent.STM (STM)
import Data.Binary (Binary (..))
import Data.Dependent.Map (DMap)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import Data.TCache (DBRef)
import Data.UUID (UUID)
import GHC.TypeLits (Symbol)
import Type.Reflection (SomeTypeRep (..), TypeRep)

type Schema = [SchemaDef]

data SchemaDef where
  FieldDef :: Type -> Symbol -> Type -> SchemaDef
  RelationDef :: Type -> Cardinality -> Symbol -> Type -> Cardinality -> SchemaDef

type LookupResult :: k -> Type
data LookupResult a where
  NotFound :: LookupResult a
  Found :: a -> LookupResult a

type IsFound :: LookupResult k -> Bool
type family IsFound r where
  IsFound (Found _) = True
  IsFound NotFound = False

type LookupField :: Schema -> Type -> Symbol -> LookupResult Type
type family LookupField schema a name where
  LookupField '[] _ _ = NotFound
  LookupField (FieldDef a name b ': rest) a name = Found b
  LookupField (_ ': rest) a name = LookupField rest a name

type LookupField_T :: LookupResult a -> a
type family LookupField_T result where
  LookupField_T (Found t) = t

type LookupRelation :: Schema -> Symbol -> LookupResult (Type, Cardinality, Type, Cardinality)
type family LookupRelation schema name where
  LookupRelation '[] _ = NotFound
  LookupRelation (RelationDef a na name b nb ': rest) name = Found '(a, na, b, nb)
  LookupRelation (_ ': rest) name = LookupRelation rest name

type LookupRelation_A :: LookupResult (Type, Cardinality, Type, Cardinality) -> Type
type family LookupRelation_A result where
  LookupRelation_A (Found '(a, _, _, _)) = a

type LookupRelation_NA :: LookupResult (Type, Cardinality, Type, Cardinality) -> Cardinality
type family LookupRelation_NA result where
  LookupRelation_NA (Found '(_, na, _, _)) = na

type LookupRelation_B :: LookupResult (Type, Cardinality, Type, Cardinality) -> Type
type family LookupRelation_B result where
  LookupRelation_B (Found '(_, _, b, _)) = b

type LookupRelation_NB :: LookupResult (Type, Cardinality, Type, Cardinality) -> Cardinality
type family LookupRelation_NB result where
  LookupRelation_NB (Found '(_, _, _, nb)) = nb

data NodeType where
  Universe :: NodeType
  DataNode :: Type -> NodeType

data Relation where
  NamedRelation :: Symbol -> Relation
  Inverse :: Symbol -> Relation
  Existence :: Type -> Relation

type Related :: Schema -> Relation -> Constraint
class Related schema rel where
  type Domain schema rel :: NodeType
  type Codomain schema rel :: NodeType
  type DomainCardinality schema rel :: Cardinality
  type CodomainCardinality schema rel :: Cardinality

instance Related schema (NamedRelation name) => Related schema (Inverse name) where
  type Domain schema (Inverse name) = Codomain schema (NamedRelation name)
  type Codomain schema (Inverse name) = Domain schema (NamedRelation name)
  type DomainCardinality schema (Inverse name) = CodomainCardinality schema (NamedRelation name)
  type CodomainCardinality schema (Inverse name) = DomainCardinality schema (NamedRelation name)

instance Related schema (Existence a) where
  type Domain schema (Existence a) = Universe
  type Codomain schema (Existence a) = DataNode a
  type DomainCardinality schema (Existence a) = One
  type CodomainCardinality schema (Existence a) = Many

instance
  IsFound (LookupRelation schema name) ~ True =>
  Related schema (NamedRelation name)
  where
  type Domain schema (NamedRelation name) = DataNode (LookupRelation_A (LookupRelation schema name))
  type Codomain schema (NamedRelation name) = DataNode (LookupRelation_B (LookupRelation schema name))
  type DomainCardinality schema (NamedRelation name) = LookupRelation_NA (LookupRelation schema name)
  type CodomainCardinality schema (NamedRelation name) = LookupRelation_NB (LookupRelation schema name)

data Field where
  NamedField :: Symbol -> Field
  RelatedNode :: Relation -> Field

type Describes :: Schema -> NodeType -> Field -> Constraint
class Describes schema nodeType field where
  type ValueType schema nodeType field :: Type

instance Related schema rel => Describes schema a (RelatedNode rel) where
  type
    ValueType schema a (RelatedNode rel) =
      Numerous (CodomainCardinality schema rel) (Node schema (Codomain schema rel))

instance
  IsFound (LookupField schema a name) ~ True =>
  Describes schema (DataNode a) (NamedField name)
  where
  type ValueType schema (DataNode a) (NamedField name) = LookupField_T (LookupField schema a name)

data Node schema a = Node (DBRef (NodeImpl schema a)) deriving (Eq, Ord)

data FieldRef schema nodeType t where
  FieldRef :: (Describes schema nodeType field, ValueType schema nodeType field ~ t) => TypeRep field -> FieldRef schema nodeType t

instance Eq (FieldRef schema nodeType t) where
  FieldRef a == FieldRef b = SomeTypeRep a == SomeTypeRep b

type FieldVal :: Schema -> Type -> Type
data FieldVal schema a where
  FieldVal :: Binary a => a -> FieldVal schema a

data NodeImpl schema nodeType = NodeImpl
  { nodeUUID :: UUID,
    nodeFields :: DMap (FieldRef schema nodeType) (FieldVal schema)
  }

describe ::
  Describes schema nodeType field =>
  Node schema nodeType ->
  Proxy field ->
  STM (ValueType schema nodeType field)
describe (Node ref) = undefined

setField ::
  Describes schema (DataNode a) (NamedField name) =>
  Node schema (DataNode a) ->
  Proxy name ->
  ValueType schema (DataNode a) (NamedField name) ->
  STM ()
setField (Node ref) _ value = undefined
