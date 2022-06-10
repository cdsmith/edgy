{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Cardinality
  ( Cardinality (..),
    Numerous,
    KnownCardinality (..),
  )
where

import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Proxy (Proxy)
import Data.Typeable (Typeable)

data Cardinality = Optional | One | Many | Some

instance Semigroup Cardinality where
  One <> c = c
  c <> One = c
  Optional <> Optional = Optional
  Optional <> _ = Many
  _ <> Optional = Many
  Some <> Some = Some
  _ <> _ = Many

instance Monoid Cardinality where
  mempty = One

type Numerous :: Cardinality -> Type -> Type
type family Numerous c t where
  Numerous Optional t = Maybe t
  Numerous One t = t
  Numerous Many t = [t]
  Numerous Some t = NonEmpty t

type KnownCardinality :: Cardinality -> Constraint
class Typeable c => KnownCardinality c where
  toCardinality :: Proxy c -> [a] -> Maybe (Numerous c a)
  fromCardinality :: Proxy c -> Numerous c a -> [a]

instance KnownCardinality Optional where
  toCardinality _ [] = Just Nothing
  toCardinality _ [x] = Just (Just x)
  toCardinality _ _ = Nothing

  fromCardinality _ Nothing = []
  fromCardinality _ (Just x) = [x]

instance KnownCardinality One where
  toCardinality _ [x] = Just x
  toCardinality _ _ = Nothing

  fromCardinality _ x = [x]

instance KnownCardinality Many where
  toCardinality _ = Just
  fromCardinality _ = id

instance KnownCardinality Some where
  toCardinality _ [] = Nothing
  toCardinality _ (x : xs) = Just (x :| xs)

  fromCardinality _ = NonEmpty.toList
