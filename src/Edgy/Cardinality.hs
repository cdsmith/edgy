{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Edgy.Cardinality
  ( Cardinality (..),
    Numerous,
    KnownCardinality (..),
  )
where

import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Typeable (Typeable)

data Cardinality = Optional | One | Many | Some

type Numerous :: Cardinality -> Type -> Type
type family Numerous c t where
  Numerous Optional t = Maybe t
  Numerous One t = t
  Numerous Many t = [t]
  Numerous Some t = NonEmpty t

type KnownCardinality :: Cardinality -> Constraint
class Typeable c => KnownCardinality c where
  listToNumerous :: forall {a}. [a] -> Maybe (Numerous c a)
  numerousToList :: forall {a}. Numerous c a -> [a]

instance KnownCardinality Optional where
  listToNumerous [] = Just Nothing
  listToNumerous [x] = Just (Just x)
  listToNumerous _ = Nothing

  numerousToList Nothing = []
  numerousToList (Just x) = [x]

instance KnownCardinality One where
  listToNumerous [x] = Just x
  listToNumerous _ = Nothing

  numerousToList x = [x]

instance KnownCardinality Many where
  listToNumerous = Just
  numerousToList = id

instance KnownCardinality Some where
  listToNumerous [] = Nothing
  listToNumerous (x : xs) = Just (x :| xs)

  numerousToList = NonEmpty.toList
