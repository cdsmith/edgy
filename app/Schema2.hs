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

module Schema2
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

type LookupField :: Schema -> Type -> Symbol -> LookupResult Type
type family LookupField schema a name where
  LookupField '[] _ _ = NotFound
  LookupField (FieldDef a name b ': rest) a name = Found b
  LookupField (_ ': rest) a name = LookupField rest a name

type LookupRelation :: Schema -> Symbol -> LookupResult (Type, Cardinality, Type, Cardinality)
type family LookupRelation schema name where
  LookupRelation '[] _ = NotFound
  LookupRelation (RelationDef a na name b nb ': rest) name = Found '(a, na, b, nb)
  LookupRelation (_ ': rest) name = LookupRelation rest name

data NodeType where
  Universe :: NodeType
  DataNode :: Type -> NodeType

data Relation where
  NamedRelation :: Symbol -> Relation
  Inverse :: Symbol -> Relation
  Existence :: Type -> Relation

type Related :: Schema -> NodeType -> Cardinality -> Relation -> NodeType -> Cardinality -> Constraint
class Related schema a na rel b nb | schema rel -> a na b nb

instance LookupRelation schema name ~ Found '(a, na, b, nb) => Related schema (DataNode a) na (NamedRelation name) (DataNode b) nb

instance Related schema a na (NamedRelation name) b nb => Related schema b nb (Inverse name) a na

instance Related schema Universe One (Existence a) (DataNode a) Many

data Field where
  NamedField :: Symbol -> Field
  RelatedNode :: Relation -> Field

type Describes :: Schema -> NodeType -> Field -> Type -> Constraint
class Describes schema nodeType field value | schema nodeType field -> value

instance LookupField schema a name ~ Found b => Describes schema (DataNode a) (NamedField name) b

instance (Related schema a na rel b nb, Numerous nb (Node schema b) ~ t) => Describes schema a (RelatedNode rel) t

data Node schema a = Node (DBRef (NodeImpl schema a)) deriving (Eq, Ord)

data FieldRef schema nodeType t where
  FieldRef :: Describes schema nodeType field t => TypeRep field -> FieldRef schema nodeType t

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
  Describes schema nodeType field t =>
  Node schema nodeType ->
  Proxy field ->
  STM t
describe (Node ref) = undefined

setField ::
  Describes schema (DataNode a) (NamedField name) t =>
  Node schema (DataNode a) ->
  Proxy name ->
  t ->
  STM ()
setField (Node ref) _ value = undefined
