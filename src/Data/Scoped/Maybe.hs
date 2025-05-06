module Data.Scoped.Maybe where

import Data.Kind
import Data.Nat
import Data.Scoped.List qualified as SList
import GHC.Generics (Generic, Generic1)
import Prelude hiding (Maybe (..))

data Maybe :: (Nat -> Type) -> Nat -> Type where
  Nothing :: Maybe a n
  Just :: a n -> Maybe a n

deriving instance (Generic1 a) => Generic1 (Maybe a)

deriving instance (Ord (a n)) => Ord (Maybe a n)

deriving instance (Eq (a n)) => Eq (Maybe a n)

deriving instance (Read (a n)) => Read (Maybe a n)

deriving instance (Show (a n)) => Show (Maybe a n)

deriving instance (Generic (a n)) => Generic (Maybe a n)

fromList :: SList.List a n -> Maybe a n
fromList SList.Nil = Nothing
fromList (x SList.:< _) = Just x

toList :: Maybe a n -> SList.List a n
toList Nothing = SList.Nil
toList (Just x) = x SList.:< SList.Nil