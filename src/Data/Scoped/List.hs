-- This module defines a type of lists indexed by their scope
-- The lists are homogenous, and every type in the list must have the
-- same scope.
-- This module is intended to be used with the OverloadedLists
-- Haskell language extension.
module Data.Scoped.List where

import Control.Monad qualified as M
import Data.Foldable qualified as F
import Data.Kind
import Data.Nat
import GHC.Generics
import GHC.IsList

-- A list of scope indexed types, all with the same scope
-- This type is isomorphic to the definition:
-- newtype List a n = MkList [a n]

data List :: (Nat -> Type) -> Nat -> Type where
  Nil :: List a n
  (:<) :: a n -> List a n -> List a n

deriving instance (Generic1 a) => Generic1 (List a)

deriving instance (Ord (a n)) => Ord (List a n)

deriving instance (Eq (a n)) => Eq (List a n)

deriving instance (Read (a n)) => Read (List a n)

deriving instance (Show (a n)) => Show (List a n)

deriving instance (Generic (a n)) => Generic (List a n)

instance Semigroup (List a n) where
  Nil <> l = l
  (x :< xs) <> l = x :< xs <> l

instance (Monoid (a n)) => Monoid (List a n) where
  mempty = Nil

-- >>> :info []
-- type List :: * -> *
-- data List a = [] | a : [a]
--   	-- Defined in ‘GHC.Types’

-- instance MonadPlus [] -- Defined in ‘GHC.Base’
-- instance Foldable [] -- Defined in ‘Data.Foldable’
-- instance MonadFail [] -- Defined in ‘Control.Monad.Fail’
-- instance Traversable [] -- Defined in ‘Data.Traversable’
-- instance Applicative [] -- Defined in ‘GHC.Base’
-- instance Functor [] -- Defined in ‘GHC.Base’
-- instance Monad [] -- Defined in ‘GHC.Base’

-- functor
map :: (IsList a, IsList b) => (Item a -> Item b) -> a -> b
map f x = fromList (fmap f (toList x))

instance IsList (List v n) where
  type Item (List v n) = v n

  fromList :: [Item (List v n)] -> List v n
  fromList = F.foldr (:<) Nil

  toList :: List v n -> [Item (List v n)]
  toList Nil = []
  toList (x :< xs) = x : toList xs

-- This type doesn't have the right kind to be
-- part of the Foldable type class. But we can redefine
-- the foldable operations anyways.
-- https://hackage.haskell.org/package/base-4.21.0.0/docs/Data-Foldable.html

fold :: (Monoid (Item l), IsList l) => l -> Item l
fold x = F.fold (toList x)

foldMap :: (Monoid m, IsList l) => (Item l -> m) -> l -> m
foldMap f x = F.foldMap f (toList x)

foldMap' :: (Monoid m, IsList l) => (Item l -> m) -> l -> m
foldMap' f x = F.foldMap' f (toList x)

foldr :: (IsList l) => (Item l -> b -> b) -> b -> l -> b
foldr f b x = F.foldr f b (toList x)

foldr' :: (IsList l) => (Item l -> b -> b) -> b -> l -> b
foldr' f b x = F.foldr' f b (toList x)

foldl :: (IsList l) => (b -> Item l -> b) -> b -> l -> b
foldl f b x = F.foldl f b (toList x)

foldl' :: (IsList l) => (b -> Item l -> b) -> b -> l -> b
foldl' f b x = F.foldl f b (toList x)

foldr1 :: (IsList l) => (Item l -> Item l -> Item l) -> l -> Item l
foldr1 f x = F.foldr1 f (toList x)

foldl1 :: (IsList l) => (Item l -> Item l -> Item l) -> l -> Item l
foldl1 f x = F.foldl1 f (toList x)

null :: (IsList l) => l -> Bool
null x = F.null (toList x)

length :: (IsList l) => l -> Int
length x = F.length (toList x)

elem :: (Eq (Item l), IsList l) => Item l -> l -> Bool
elem a x = F.elem a (toList x)

maximum :: (Ord (Item l), IsList l) => l -> Item l
maximum x = F.maximum (toList x)

minimum :: (Ord (Item l), IsList l) => l -> Item l
minimum x = F.maximum (toList x)

sum :: (Num (Item l), IsList l) => l -> Item l
sum x = F.sum (toList x)

product :: (Num (Item l), IsList l) => l -> Item l
product x = F.product (toList x)

any :: (IsList l) => (Item l -> Bool) -> l -> Bool
any f x = F.any f (toList x)

all :: (IsList l) => (Item l -> Bool) -> l -> Bool
all f x = F.all f (toList x)

-- >>> :t M.mapM @[]
-- M.mapM @[] :: Monad m => (a -> m b) -> [a] -> m [b]

mapM :: (Monad m, IsList a, IsList b) => (Item a -> m (Item b)) -> a -> m b
mapM f x = fromList <$> M.mapM f (toList x)

mapM_ :: (Monad m, IsList l) => (Item l -> m b) -> l -> m ()
mapM_ f x = M.mapM_ f (toList x)

zipWithM_ f x1 x2 = M.zipWithM_ f (toList x1) (toList x2)
