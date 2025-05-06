-- | N-ary binding
-- This file does not need to be qualified when imported. Instead, it postfixes
-- all operations with 1/2/N to distinguish them.
module AutoEnv.Bind.PatN
  ( module AutoEnv.Classes,

    -- * single binder --
    Bind1 (..),
    bind1,
    unbind1,
    unbindl1,
    getBody1,
    instantiate1,
    unbindWith1,
    instantiateWith1,
    applyUnder1,

    -- * double binder --
    Bind2 (..),
    bind2,
    unbind2,
    getBody2,
    instantiate2,
    unbindWith2,
    instantiateWith2,
    applyUnder2,

    -- * N-ary binder ---
    BindN (..),
    bindN,
    unbindN,
    unbindlN,
    getBodyN,
    instantiateN,
    unbindWithN,
    instantiateWithN,
    applyUnderN,
  )
where

import AutoEnv.Bind.Pat qualified as Pat
import AutoEnv.Classes
import AutoEnv.Env
import Data.Fin (Fin)
import Data.Fin qualified as Fin
import Data.Nat
import Data.SNat
import Data.Vec (Vec)
import Data.Vec qualified as Vec

----------------------------------------------------------------
-- N-ary patterns
----------------------------------------------------------------

-- * A pattern that binds `p` variables

newtype PatN (p :: Nat) where
  PatN :: SNat p -> PatN p

instance (SNatI p) => Sized (PatN p) where
  type Size (PatN p) = p
  size (PatN sn) = sn

type BindN v c m n = Pat.Bind v c (PatN m) n

bindN :: forall m v c n. (Subst v c, SNatI m) => c (m + n) -> BindN v c m n
bindN = Pat.bind (PatN (snat @m))

unbindN :: forall m v c n d. (Subst v c, SNatI n, SNatI m) => BindN v c m n -> ((SNatI (m + n)) => c (m + n) -> d) -> d
unbindN bnd f = Pat.unbind bnd (const f)

unbindlN :: forall m v c n. (Subst v c, SNatI m) => BindN v c m n -> c (m + n)
unbindlN = Pat.getBody

getBodyN :: forall m v c n. (Subst v c, SNatI m) => BindN v c m n -> c (m + n)
getBodyN = Pat.getBody

unbindWithN ::
  (SubstVar v, SNatI m) =>
  BindN v c m n ->
  (forall m1. Env v m1 n -> c (m + m1) -> d) ->
  d
unbindWithN b f = Pat.unbindWith b (const f)

instantiateN :: (Subst v c, SNatI m) => BindN v c m n -> Vec m (v n) -> c n
instantiateN b v = Pat.instantiate b (fromVec v)

instantiateWithN ::
  forall m v c d n.
  (SubstVar v, SNatI n, SNatI m) =>
  BindN v c m n ->
  Vec m (v n) ->
  (forall m n. Env v m n -> c m -> d n) ->
  d n
instantiateWithN b v f =
  unbindWithN b (f . appendE (snat @m) (fromVec v))

applyUnderN ::
  (Subst v c2, SNatI m) =>
  (forall m n. Env v m n -> c1 m -> c2 n) ->
  Env v n1 n2 ->
  BindN v c1 m n1 ->
  BindN v c2 m n2
applyUnderN = Pat.applyUnder

----------------------------------------------------------------
-- Single binder
----------------------------------------------------------------

-- A single binder is a pattern binding with
-- "SNat 1" as the pattern

type Bind1 v c n = Pat.Bind v c (PatN N1) n

bind1 :: (Subst v c) => c (S n) -> Bind1 v c n
bind1 = Pat.bind (PatN s1)

getBody1 ::
  forall v c n.
  (Subst v c) =>
  Bind1 v c n ->
  c (S n)
getBody1 = Pat.getBody

unbind1 ::
  forall v c n d.
  (SNatI n, Subst v c) =>
  Bind1 v c n ->
  ((SNatI (S n)) => c (S n) -> d) ->
  d
unbind1 b f = f (Pat.getBody b)

unbindl1 :: forall v c n. (Subst v c) => Bind1 v c n -> c (S n)
unbindl1 = Pat.getBody

unbindWith1 ::
  (SubstVar v) =>
  Bind1 v c n ->
  (forall m. Env v m n -> c (S m) -> d) ->
  d
unbindWith1 b f = Pat.unbindWith b (const f)

instantiate1 :: (Subst v c) => Bind1 v c n -> v n -> c n
instantiate1 b v1 = Pat.instantiate b (v1 .: zeroE)

instantiateWith1 ::
  (SubstVar v) =>
  Bind1 v c n ->
  v n ->
  (forall m n. Env v m n -> c m -> d n) ->
  d n
instantiateWith1 b v1 f =
  unbindWith1 b (\r e -> f (v1 .: r) e)

applyUnder1 ::
  (Subst v c2) =>
  (forall m n. Env v m n -> c1 m -> c2 n) ->
  Env v n1 n2 ->
  Bind1 v c1 n1 ->
  Bind1 v c2 n2
applyUnder1 = Pat.applyUnder

----------------------------------------------------------------
-- Double binder
----------------------------------------------------------------

-- A double binder is a pattern binding with
-- "SNat 2" as the pattern

type Bind2 v c n = Pat.Bind v c (PatN N2) n

bind2 :: (Subst v c) => c (S (S n)) -> Bind2 v c n
bind2 = Pat.bind (PatN s2)

getBody2 ::
  forall v c n.
  (Subst v c) =>
  Bind2 v c n ->
  c (S (S n))
getBody2 = Pat.getBody

unbind2 ::
  forall v c n d.
  (Subst v c) =>
  Bind2 v c n ->
  (c (S (S n)) -> d) ->
  d
unbind2 b f = f (getBody2 b)

unbindWith2 ::
  (SubstVar v) =>
  Bind2 v c n ->
  (forall m. Env v m n -> c (S (S m)) -> d) ->
  d
unbindWith2 b f = Pat.unbindWith b (const f)

instantiate2 :: (Subst v c) => Bind2 v c n -> v n -> v n -> c n
instantiate2 b v1 v2 = Pat.instantiate b (v1 .: (v2 .: zeroE))

instantiateWith2 ::
  (SubstVar v, SNatI n) =>
  Bind2 v c n ->
  v n ->
  v n ->
  (forall m n. Env v m n -> c m -> d n) ->
  d n
instantiateWith2 b v1 v2 f =
  unbindWith2 b (\r e -> f (v1 .: (v2 .: r)) e)

applyUnder2 ::
  (Subst v c2) =>
  (forall m n. Env v m n -> c1 m -> c2 n) ->
  Env v n1 n2 ->
  Bind2 v c1 n1 ->
  Bind2 v c2 n2
applyUnder2 = Pat.applyUnder