{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}

-- |
-- Module      : Data.Fin
-- Description : Bounded natural numbers
-- Stability   : experimental
--
-- This file re-exports definitions from fin's Data.Fin, while adding a few more
-- that are relevant to this context. Like Data.Fin, is meant to be used qualified.
--       import Fin (Fin (..))
--       import qualified Fin as Fin
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PackageImports #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
module Data.Fin(
  Nat(..), SNat(..),
  Fin(..),
  toNat, fromNat, toInteger,
  mirror,
  absurd,
  universe,
  f0,f1,f2,
  invert,
  shiftN,
  shift1,
  weakenFin,
  weakenFinRight,
  weaken1Fin,
  weaken1FinRight,
  strengthen1Fin,
  strengthenRecFin
 ) where

import Data.Nat
import Data.SNat
import "fin" Data.Fin hiding (cata)
import Data.Proxy (Proxy (..))
import Data.SNat
-- for efficient rescoping
import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- toInt
-------------------------------------------------------------------------------

-- >>> :t toInteger
-- toInteger :: Integral a => a -> Integer

-- The `toInteger` instance has an unnecessary
-- type class constraint (NatI n) for Fin. So we
-- also include this class for simple conversion.
instance ToInt (Fin n) where
  toInt :: Fin n -> Int
  toInt FZ = 0
  toInt (FS x) = 1 + toInt x

-- >>> [minBound .. maxBound] :: [Fin N3]
-- [0,1,2]

-- list all numbers up to some size
-- >>> universe :: [Fin N3]
-- [0,1,2]

-- >>> :info Fin

-- | Convert an "index" Fin to a "level" Fin and vice versa
invert :: forall n. (SNatI n) => Fin n -> Fin n
invert f = case snat @n of
  SZ -> case f of {}
  SS -> maxBound - f

-------------------------------------------------------------------------------
-- Shifting and weakening
-------------------------------------------------------------------------------

-- Weakening: Adding a new binding to the context without changing existing
-- indices.
-- Shifting: Adjusting the indices of free variables within a term to
-- reflect a new binding added to the context.

-- Shifting functions add some specified amount to the given
-- `Fin` value, also incrementing its type.

-- Shifting is implemented in the Data.Fin libary using the `weakenRight`
-- function, which changes the value of a Fin and its type.
-- >>> :t weakenRight
-- weakenRight :: SNatI n => Proxy n -> Fin m -> Fin (Plus n m)

-- >>> weakenRight (Proxy :: Proxy N1) (f1 :: Fin N2) :: Fin N3
-- 2

-- In this module, we call the same operation `shiftN` and give
-- it a slightly more convenient interface.
-- >>> shiftN s1 (f1 :: Fin N2)
-- 2

-- increment by a fixed amount (on the left)
shiftN :: forall n m. SNat n -> Fin m -> Fin (n + m)
shiftN p f = withSNat p $ weakenRight (Proxy :: Proxy n) f

shift1 :: Fin m -> Fin (S m)
shift1 = shiftN s1

-- We could also include a dual function, which increments on the right
-- but we haven't needed that operation anywhere.

-------------------------------------------------------------------------------
-- Weakening
-------------------------------------------------------------------------------

-- Weakenening changes the bound of a nat-indexed type without changing
-- its value.
-- These operations can either be defined for the n-ary case (as in Fin below)
-- or be defined in terms of a single-step operation.
-- However, as both of these operations are identity functions,
-- it is justified to use unsafeCoerce.

-- The corresponding function in the Data.Fin library is `weakenLeft`.
-- >>> :t weakenLeft
-- weakenLeft :: SNatI n => Proxy m -> Fin n -> Fin (Plus n m)
-- This function does not change the value, it only changes its type.
-- >>> weakenLeft (Proxy :: Proxy N1) (f1 :: Fin N2) :: Fin N3
-- 1

-- We could use the following definition:
--
-- weakenFin m f = withSNat m $ weakenLeft (Proxy :: Proxy m) f
--
-- But, by using an `unsafeCoerce` implementation, we can avoid the
-- `SNatI n` constraint in the type of this operation.

-- >>> weakenFin (Proxy :: Proxy N1) (f1 :: Fin N2) :: Fin N3
-- 1

-- | weaken the bound of a Fin by an arbitrary amount
weakenFin :: proxy m -> Fin n -> Fin (m + n)
weakenFin _ f = unsafeCoerce f

-- | weaken the bound of a Fin by 1.
weaken1Fin :: Fin n -> Fin (S n)
weaken1Fin = weakenFin s1

-- | weaken the bound of of a Fin by an arbitrary amount on the right.
-- This is also an identity function
-- >>> weakenFinRight (s1 :: SNat N1) (f1 :: Fin N2) :: Fin N3
-- 1
weakenFinRight :: proxy m -> Fin n -> Fin (n + m)
weakenFinRight m f = unsafeCoerce f

-- | weaken th ebound of a Fin by 1.
weaken1FinRight :: Fin n -> Fin (n + N1)
weaken1FinRight = weakenFinRight s1

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

-- Convenient names for fin values. These have polymorphic types so they
-- will work in any scope. (These are also called fin0, fin1, fin2, etc
-- in Data.Fin)

f0 :: Fin (S n)
f0 = FZ

f1 :: Fin (S (S n))
f1 = FS f0

f2 :: Fin (S (S (S n)))
f2 = FS f1

f3 :: Fin (S (S (S (S n))))
f3 = FS f2

-- >>> f2
-- 2

-------------------------------------------------------------------------------
-- Strengthening
-------------------------------------------------------------------------------

-- With strengthening, we make sure that variable f0 is not used,
-- and we decrement all other indices by 1. This allows us to
-- also decrement the scope by one.

--- >>> strengthen1Fin (f0 :: Fin (S N3)) :: Maybe (Fin N3)
-- Nothing

-- >>> strengthen1Fin (f1 :: Fin (S N3)) :: Maybe (Fin N3)
-- Just 0

-- >>> strengthen1Fin (f2 :: Fin (S N3)) :: Maybe (Fin N3)
-- Just 1

strengthen1Fin :: forall n. (SNatI n) => Fin (S n) -> Maybe (Fin n)
strengthen1Fin = strengthenRecFin s0 s1 snat

-- We implement strengthening with the following operation that
-- generalizes the induction hypothesis, so that we can strengthen
-- in the middle of the scope. The scope of the Fin should have the form
-- k + (m + n)

-- Indices in the middle part of the scope `m` are "strengthened" away.

--- >>> strengthenRecFin s1 s1 s2 (f1 :: Fin (N1 + N1 + N2)) :: Maybe (Fin (N1 + N2))
-- Nothing

-- Variables that are in the first part of the scope `k` (the ones that have
-- most recently entered the context) do not change when strengthening.

--- >>> strengthenRecFin s1 s1 s2 (f0 :: Fin (N1 + N1 + N2))
-- Just 0

-- Variables in the last part of the scope `n` are decremented by strengthening

-- >>> strengthenRecFin s1 s1 s2 (f2 :: Fin (N1 + N1 + N2)) :: Maybe (Fin N3)
-- Just 1

-- >>> strengthenRecFin s1 s1 s2 (f3 :: Fin (N1 + N1 + N2)) :: Maybe (Fin N3)
-- Just 2

strengthenRecFin :: SNat k -> SNat m -> SNat n -> Fin (k + (m + n)) -> Maybe (Fin (k + n))
strengthenRecFin SZ SZ n x = Just x -- Base case: k = 0, m = 0
strengthenRecFin SZ (snat_ -> SS_ m) n FZ = Nothing
-- Case: k = 0, m > 0, and x is in the `m` range
strengthenRecFin SZ (snat_ -> SS_ m) n (FS x) =
  strengthenRecFin SZ m n x
strengthenRecFin (snat_ -> SS_ k) m n FZ = Just FZ
-- Case: x < k, leave it alone
strengthenRecFin (snat_ -> SS_ k) m n (FS x) =
  FS <$> strengthenRecFin k m n x
