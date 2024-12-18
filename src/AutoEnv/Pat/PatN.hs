module AutoEnv.Pat.PatN where

import Data.Nat
import AutoEnv.Classes
import qualified AutoEnv.Pat.Simple as Pat
import AutoEnv.Env

----------------------------------------------------------------
-- N-ary patterns
----------------------------------------------------------------

-- * A pattern that binds `p` variables
data PatN (p :: Nat) where
  PatN :: SNat p -> PatN p

instance (SNatI p) => Pat.Sized (PatN p) where
  type Size (PatN p) = p
  size (PatN sn) = sn

----------------------------------------------------------------
-- Double binder
----------------------------------------------------------------

-- A double binder is just a pattern binding with
-- "SNat 2" as the pattern

s2' :: SNat Z
s2' = snat

type Bind2 v c n = Pat.Bind v c (PatN N2) n

bind2 :: (Subst v c) => c (S (S n)) -> Bind2 v c n
bind2 = Pat.bind (PatN s2)

unbind2 :: forall v c n. (Subst v v, Subst v c) => Bind2 v c n -> c (S (S n))
unbind2 = Pat.getBody

unbind2With ::
  (SubstVar v) =>
  Bind2 v c n ->
  (forall m. Env v m n -> c (S (S m)) -> d) ->
  d
unbind2With b f = Pat.unBindWith b (const f)

instantiate2 :: (Subst v c) => Bind2 v c n -> v n -> v n -> c n
instantiate2 b v1 v2 = Pat.instantiate b (v1 .: (v2 .: zeroE))

instantiate2With ::
  (SubstVar v, SNatI n) =>
  Bind2 v c n ->
  v n ->
  v n ->
  (forall m n. Env v m n -> c m -> c n) ->
  c n
instantiate2With b v1 v2 f =
  unbind2With b (\r e -> f (v1 .: (v2 .: r)) e)
