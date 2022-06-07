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

data Cardinality = Optional | One | Many | Some

type Numerous :: Cardinality -> Type -> Type
type family Numerous c t where
  Numerous Optional t = Maybe t
  Numerous One t = t
  Numerous Many t = [t]
  Numerous Some t = NonEmpty t

type KnownCardinality :: Cardinality -> Constraint
class KnownCardinality c where
  collection :: Proxy c -> [a] -> Maybe (Numerous c a)
  fromCardinality :: Proxy c -> Numerous c a -> [a]

instance KnownCardinality Optional where
  collection _ [] = Just Nothing
  collection _ [x] = Just (Just x)
  collection _ _ = Nothing

  fromCardinality _ Nothing = []
  fromCardinality _ (Just x) = [x]

instance KnownCardinality One where
  collection _ [x] = Just x
  collection _ _ = Nothing

  fromCardinality _ x = [x]

instance KnownCardinality Many where
  collection _ = Just
  fromCardinality _ = id

instance KnownCardinality Some where
  collection _ [] = Nothing
  collection _ (x : xs) = Just (x :| xs)

  fromCardinality _ = NonEmpty.toList
