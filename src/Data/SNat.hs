module Data.SNat
  ( -- module Data.Type.Nat,
    Nat (..),
    toNatural,
    fromNatural,
    SNat (..),
    snatToNat,
    SNatI (..),
    snat,
    withSNat,
    reify,
    reflect,
    type (+),
    N0,
    N1,
    N2,
    N3,
    s0,
    s1,
    s2,
    s3,
    sPlus,
    axiomSus,
    axiomPlusZ,
    axiomAssoc,
    SNat_ (..),
    snat_,
    pred,
    succ,
    ToInt (..),
  )
where

-- similar to https://hackage.haskell.org/package/fin-0.3.1/docs/Data-Nat.html#t:Nat
-- Singleton nats are purely runtime

import Data.Type.Equality
import Data.Type.Nat
import Test.QuickCheck
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (pred, succ)

-----------------------------------------------------
-- axioms (use unsafeCoerce)
-----------------------------------------------------

-- Monoid properties for plus
axiomPlusZ :: forall m. m + Z :~: m
axiomPlusZ = unsafeCoerce Refl

axiomAssoc :: forall p m n. p + (m + n) :~: (p + m) + n
axiomAssoc = unsafeCoerce Refl

-- Another property about addition
-- Somewhat sus. Can we get rid of this?
axiomSus :: forall m n. m + S n :~: S (m + n)
axiomSus = unsafeCoerce Refl

-----------------------------------------------------
-- Nats (singleton nats and implicit singletons)
-----------------------------------------------------

type N0 = Z

type N1 = S N0

type N2 = S N1

type N3 = S N2

---------------------------------------------------------
-- Singletons and instances
---------------------------------------------------------

s0 :: SNat N0
s0 = snat

s1 :: SNat N1
s1 = snat

s2 :: SNat N2
s2 = snat

s3 :: SNat N3
s3 = snat

instance (SNatI n) => Arbitrary (SNat n) where
  arbitrary :: (SNatI n) => Gen (SNat n)
  arbitrary = pure snat

class ToInt a where
  toInt :: a -> Int

instance ToInt (SNat n) where
  toInt :: SNat n -> Int
  toInt = fromInteger . toInteger . snatToNat

---------------------------------------------------------
-- Addition
---------------------------------------------------------

type family (n :: Nat) + (m :: Nat) :: Nat where
  m + n = Plus m n

sPlus :: forall n1 n2. SNat n1 -> SNat n2 -> SNat (n1 + n2)
sPlus SZ n = n
sPlus x@SS y = withSNat (sPlus (pred x) y) SS

-- >>> reflect $ sPlus s3 s1
-- 4

---------------------------------------------------------
-- View pattern access to the predecessor
---------------------------------------------------------

data SNat_ n where
  SZ_ :: SNat_ Z
  SS_ :: SNat n -> SNat_ (S n)

snat_ :: SNat n -> SNat_ n
snat_ SZ = SZ_
snat_ SS = SS_ snat

pred :: SNat (S n) -> SNat n
pred SS = snat

succ :: SNat n -> SNat (S n)
succ x = withSNat x SS