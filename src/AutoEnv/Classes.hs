-- |
-- Module      : AutoEnv.Classes
-- Description : Type class definitions
-- Stability   : experimental
module AutoEnv.Classes where

import AutoEnv.Lib
import Data.Fin
import Data.Foldable
import Data.Vec qualified as Vec

-- | An environment (or explicit substitution) that map
-- indices bounded by `m`, to values of type `v n`
-- For now, we represent this directly as a function,
-- but we might want to change that. So we wrap it in
-- a newtype to hide the representation.
-- newtype Env (v :: Nat -> Type) (m :: Nat) (n :: Nat) =
--  Env { applyEnv :: Fin m -> v n }

----------------------------------------------------------
-- Substitution, free variables
----------------------------------------------------------

-- | Well-scoped types that can be the range of
-- an environment. This should generally be the `Var`
-- constructor from the syntax.
-- class SubstVar (v :: Nat -> Type) where
--  var :: Fin n -> v n

-- | Apply the environment throughout a term of
-- type `c n`, replacing variables with values
-- of type `v m`
-- class (SubstVar v) => Subst v c where
--  applyE :: Env v n m -> c n -> c m

class Shiftable t where
  shift :: SNat k -> t n -> t (k + n)
  -- default shift :: forall v k n. (SubstVar v, Subst v t) => SNat k -> t n -> t (k + n)
  -- shift = shiftFromApplyE @v

-- | Does a variable appear free?
class FV (t :: Nat -> Type) where
  appearsFree :: Fin n -> t n -> Bool

----------------------------------------------------------

-- * Strengthening

----------------------------------------------------------

-- entry point for eliminating the most recently bound variable from the scope (if unused)
strengthen :: forall n t. (Strengthen t, SNatI n) => t (S n) -> Maybe (t n)
strengthen = strengthenRec s0 s1 (snat :: SNat n)

-- Strengthening cannot be implemented through substitution because it
-- must fail if the term uses invalid variables. Therefore, we make a
-- class of scoped types that can be strengthened.
class Strengthen t where
  -- generalize strengthening -- remove m variables from the middle of the scope
  strengthenRec :: SNat k -> SNat m -> SNat n -> t (k + (m + n)) -> Maybe (t (k + n))

  -- Remove a single variable from the middle of the scope
  strengthenOneRec :: forall k n. SNat k -> SNat n -> t (k + S n) -> Maybe (t (k + n))
  strengthenOneRec k = strengthenRec k s1

-- n-ary version of strengthen
strengthenN :: forall m n t. (Strengthen t, SNatI n) => SNat m -> t (m + n) -> Maybe (t n)
strengthenN m = strengthenRec s0 m (snat :: SNat n)

---------------------------------------------------------

instance FV Fin where
  appearsFree = (==)

instance Strengthen Fin where
  strengthenRec :: SNat k -> SNat m -> SNat n -> Fin (k + (m + n)) -> Maybe (Fin (k + n))
  strengthenRec = strengthenRecFin

-- >>> strengthenOne' (SS (SS SZ)) (FZ :: Fin N3) :: Maybe (Fin N2)
-- Just 0

-- >>> strengthen' (SS (SS SZ)) (SS SZ) (FZ :: Fin N3) :: Maybe (Fin N1)
-- Just 0

----------------------------------------------------------
-- Type classes for patterns
----------------------------------------------------------

-- | Calculate the number of binding variables in the pattern
-- This number does not need to be an explicit parameter of the type
-- so that we have flexibility about what types we can use as
-- patterns.
class Sized (t :: Type) where
  -- Retrieve size from the type (number of variables bound by the pattern)
  type Size t :: Nat

  -- Access size as a term
  size :: t -> SNat (Size t)

-- | Pairs of types that can be compared with each other as patterns
class PatEq (t1 :: Type) (t2 :: Type) where
  patEq :: t1 -> t2 -> Maybe (Size t1 :~: Size t2)

---------------------------------------------------------
-- Pattern Class Instances for Prelude and Lib Types
---------------------------------------------------------

-- ** LocalNames

instance Sized LocalName where
  type Size LocalName = N1
  size _ = s1

instance PatEq LocalName LocalName where
  patEq p1 p2 = Just Refl

-- ** SNats

instance Sized (SNat n) where
  type Size (SNat n) = n
  size n = n

instance PatEq (SNat n1) (SNat n2) where
  patEq = testEquality

-- ** Vectors

instance Sized (Vec n a) where
  type Size (Vec n a) = n
  size = Vec.vlength

instance (Eq a) => PatEq (Vec n1 a) (Vec n2 a) where
  patEq VNil VNil = Just Refl
  patEq (x ::: xs) (y ::: ys)
    | x == y,
      Just Refl <- patEq xs ys =
        Just Refl
  patEq _ _ = Nothing

-- ** Unit (trivial)

instance Sized () where type Size () = N0; size _ = SZ

instance PatEq () () where patEq _ _ = Just Refl

-- ** Pairs

instance (Sized a, Sized b) => Sized (a, b) where
  type Size (a, b) = Size a + Size b
  size (x, y) = sPlus (size x) (size y)

instance (PatEq a1 a2, PatEq b1 b2) => PatEq (a1, b1) (a2, b2) where
  patEq (x1, y1) (x2, y2)
    | Just Refl <- patEq x1 x2,
      Just Refl <- patEq y1 y2 =
        Just Refl
  patEq _ _ = Nothing

------------------------------------------
