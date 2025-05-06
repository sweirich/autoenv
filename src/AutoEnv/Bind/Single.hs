-- | Simplest form of binding: a single variable
-- with no other information stored with the binder
-- (This is a specialization of n-ary binding.)
module AutoEnv.Bind.Single
  ( module AutoEnv.Classes,
    Bind (..),
    bind,
    unbind,
    unbindl,
    getBody,
    instantiate,
    unbindWith,
    instantiateWith,
    applyUnder,
  )
where

import AutoEnv
import AutoEnv.Bind.PatN
import AutoEnv.Classes

type Bind v c n = Bind1 v c n

bind :: (Subst v c) => c (S n) -> Bind v c n
bind = bind1

unbind :: forall v c n d. (SNatI n, Subst v c) => Bind v c n -> ((SNatI (S n)) => c (S n) -> d) -> d
unbind = unbind1

unbindl :: (Subst v c) => Bind v c n -> c (S n)
unbindl = unbindl1

getBody :: forall v c n. (Subst v c) => Bind v c n -> c (S n)
getBody = getBody1

instantiate :: (Subst v c) => Bind v c n -> v n -> c n
instantiate = instantiate1

unbindWith :: (SubstVar v) => Bind v c n -> (forall m. Env v m n -> c (S m) -> d) -> d
unbindWith = unbindWith1

instantiateWith :: (SubstVar v) => Bind v c n -> v n -> (forall m n. Env v m n -> c m -> d n) -> d n
instantiateWith = instantiateWith1

applyUnder :: (Subst v c2) => (forall m n. Env v m n -> c1 m -> c2 n) -> Env v n1 n2 -> Bind v c1 n1 -> Bind v c2 n2
applyUnder = applyUnder1

{-
----------------------------------------------------------------
-- Single binders
----------------------------------------------------------------

-- | Type for a single binders
-- includes an delayed substitution plus a term with an
-- extra free variable for the binder
-- n is the number of free variables in the term
data Bind v c (n :: Nat) where
  Bind :: Env v m n -> c (S m) -> Bind v c n

-- | The substitution operation composes the explicit
-- substitution with the one stored at the binder
instance (Subst v v) => Subst v (Bind v c) where
  applyE :: (Subst v v) => Env v n m -> Bind v c n -> Bind v c m
  applyE env1 (Bind env2 m) = Bind (env2 .>> env1) m

instance (Subst v v) => GSubst v (Bind v c) where
  gsubst = applyE

instance (Subst v v, Subst v c, FV c) => FV (Bind v c) where
  appearsFree n b = appearsFree (FS n) (unbind b)

-- | create a single binder
bind :: (Subst v c) => c (S n) -> Bind v c n
bind = Bind idE

-- | access the body of the binder  (inverse of bind)
unbind :: forall v c n. (Subst v v, Subst v c) => Bind v c n -> c (S n)
unbind (Bind r t) = applyE (up r) t

-- | access the body of the binder
getBody :: forall v c n. (Subst v v, Subst v c) => Bind v c n -> c (S n)
getBody = unbind

-- | instantiate a binder with a term
instantiate :: (Subst v c) => Bind v c n -> v n -> c n
instantiate b v = unbindWith b (\r e -> applyE (v .: r) e)

-- | apply an environment-parameterized function while
-- instantiating
instantiateWith ::
  Bind v c n ->
  v n ->
  (forall m n. Env v m n -> c m -> d n) ->
  d n
instantiateWith (Bind r a) v f = f (v .: r) a

-- | unbind a binder and apply the function to the argument and subterm
unbindWith ::
  (SubstVar v) =>
  Bind v c n ->
  (forall m. Env v m n -> c (S m) -> d) ->
  d
unbindWith (Bind r t) f = f r t

-- | apply an environment-parameterized function & environment
-- underneath a binder
applyUnder ::
  (Subst v c2) =>
  (forall m n. Env v m n -> c1 m -> c2 n) ->
  Env v n1 n2 ->
  Bind v c1 n1 ->
  Bind v c2 n2
applyUnder f r2 (Bind r1 t) =
  bind (f (up (r1 .>> r2)) t)

instance (SubstVar v, Subst v v, Subst v c, Strengthen c) =>
  Strengthen (Bind v c) where

  strengthenRec :: forall k m n v c. (SubstVar v, Subst v v, Subst v c, Strengthen c) =>
    SNat k -> SNat m -> SNat n -> Bind v c (k + (m + n)) -> Maybe (Bind v c (k + n))
  strengthenRec k m n bnd =
      bind <$> strengthenRec (SNat.succ k) m n (unbind bnd)

-- | Create a substitution that instantiates a binder
-- with `a` and shifts at the same time. This is useful for
-- opening a pi-type after n-ary binding in pattern matching
-- TODO: better name?
-- TODO: more efficient implementation?
instantiateWeakenEnv ::
  forall p n v c.
  (SubstVar v) =>
  SNat p ->
  SNat n ->
  v (p + n) ->
  Env v (S n) (p + n)
instantiateWeakenEnv p n a =
  a .: shiftNE p

-- | instantiate a single binder with a term from a larger scope
-- this simultaneously shifts the body of the bind to that scope
-- TODO: add a version of instantiateShift for pattern binding
instantiateShift ::
  forall p n v c.
  (SubstVar v, Subst v v, Subst v c, SNatI n) =>
  SNat p ->
  Bind v c n ->
  v (p + n) ->
  c (p + n)
instantiateShift p b a =
  applyE (a .: shiftNE p) (unbind b)
  -}