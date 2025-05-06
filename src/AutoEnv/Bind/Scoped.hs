-- | A "Scoped" pattern binds variables but
-- can also include subterms that reference
-- free variables that are already in scope.
-- This is useful for type annotations and telescopes.
-- The pattern type must have kind `Nat -> Type`
-- For a simpler interface, see AutoEnv.Bind.Pat
module AutoEnv.Bind.Scoped where

import AutoEnv
import AutoEnv.Bind.Pat qualified as Pat
import AutoEnv.DependentScope (WithData (..))
import AutoEnv.DependentScope qualified as DS
import Data.Fin qualified as Fin
import Data.Vec qualified as Vec

----------------------------------------------------------
-- Sized type class for patterns
----------------------------------------------------------

-- Scoped patterns have kinds :: Nat -> Nat -> Type where
-- the first parameter is `p`, the number of variables that pattern
-- binds, and the second parameter is `n`, the scope of for any
-- terms that appear inside the pattern.

-- Crucially, the number of variables bound by the pattern
-- shouldn't depend on the scope. We manifest that with the
-- associated type `ScopedSize :: Nat -> Type` and the constraint
-- that it must be the same as Size for any number of bound variables.

class (Sized (t p), Size (t p) ~ ScopedSize t) => EqSized t p

instance (Sized (t p), Size (t p) ~ ScopedSize t) => EqSized t p

-- this is equivalent to (Size (t p) ~ ScopedSize pat
class (forall p. EqSized pat p) => ScopedSized pat where
  type ScopedSize (pat :: Nat -> Type) :: Nat

-- For convenience, we give the `size` function a type that mentions
-- `ScopedSize` instead of `Size`.
scopedSize :: forall pat p. (ScopedSized pat) => pat p -> SNat (ScopedSize pat)
scopedSize = size

-- And we give the `names` function a similar type
scopedNames ::
  (ScopedSized pat, Named name (pat p)) =>
  pat p ->
  Vec (ScopedSize pat) name
scopedNames = names

scopedData ::
  forall (pat :: Nat -> Type) (p :: Nat) (u :: Type) (s :: Nat -> Type) (n :: Nat).
  (ScopedSized pat, WithData (pat p) u s n) =>
  pat p ->
  DS.Scope u s (ScopedSize pat) n
scopedData p = get
  where
    -- The typechecker needs help...
    get :: (Size (pat p) ~ ScopedSize pat) => DS.Scope u s (ScopedSize pat) n
    get = getData @(pat p) @u @s @n p

scopedPatEq ::
  (ScopedSized pat1, ScopedSized pat2, PatEq (pat1 p1) (pat2 p2)) =>
  pat1 p1 ->
  pat2 p2 ->
  Maybe (ScopedSize pat1 :~: ScopedSize pat2)
scopedPatEq = patEq

-- This file uses `ScopedSize`, `scopedSize`, and `scopedNames`,
-- instead of `Size`, `size`, and `names` throughout.

----------------------------------------------------------
-- Scoped Pattern binding
----------------------------------------------------------

-- The `Bind` type binds (ScopedSize p) variables.
-- Patterns can also include free occurrences of variables so
-- they are also indexed by a scope level.
-- As in `Bind` above, this data structure includes a delayed
-- substitution for the variables in the body of the binder.
data Bind v c (pat :: Nat -> Type) (n :: Nat) where
  Bind ::
    pat n ->
    Env v m n ->
    c (ScopedSize pat + m) ->
    Bind v c pat n

-- | Create a `Bind` with an identity substitution.
bind ::
  forall v c pat n.
  (ScopedSized pat, Subst v c) =>
  pat n ->
  c (ScopedSize pat + n) ->
  Bind v c pat n
bind pat = Bind pat idE

-- | Access the pattern of a pattern binding
getPat :: Bind v c pat n -> pat n
getPat (Bind pat env t) = pat

-- | Access the body of a pattern binding.
-- The pattern type determines the number of variables
-- bound in the pattern
getBody ::
  forall v c pat n.
  (ScopedSized pat, Subst v v, Subst v c) =>
  Bind v c pat n ->
  c (ScopedSize pat + n)
getBody (Bind (pat :: pat n) (env :: Env v m n) t) =
  applyE @v @c @(ScopedSize pat + m) (upN (scopedSize pat) env) t

instantiate ::
  forall v c pat n.
  (forall n. ScopedSized pat, Subst v c) =>
  Bind v c pat n ->
  Env v (ScopedSize pat) n ->
  c n
instantiate b e =
  unBindWith
    b
    (\p r t -> withSNat (scopedSize p) $ applyE (e .++ r) t)

instantiateWith ::
  (ScopedSized pat, SubstVar v) =>
  Bind v c pat n ->
  Env v (ScopedSize pat) n ->
  (forall m n. Env v m n -> c m -> c n) ->
  c n
instantiateWith b v f =
  unBindWith b (\p r e -> withSNat (scopedSize p) $ f (v .++ r) e)

unbind ::
  forall v c pat n d.
  (SNatI n, forall n. ScopedSized pat, Subst v v, Subst v c) =>
  Bind v c pat n ->
  ((SNatI (ScopedSize pat + n)) => pat n -> c (ScopedSize pat + n) -> d) ->
  d
unbind bnd f =
  withSNat (sPlus (scopedSize (getPat bnd)) (snat @n)) $
    f (getPat bnd) (getBody bnd)

unbindl :: (SNatI n, Subst v c, ScopedSized pat) => Bind v c pat n -> (pat n, c (ScopedSize pat + n))
unbindl bnd = (getPat bnd, getBody bnd)

-- | Apply a function to the pattern, suspended environment and body
-- in a pattern binding
unBindWith ::
  (forall n. Sized (pat n), SubstVar v) =>
  Bind v c pat n ->
  (forall m. pat n -> Env v m n -> c (ScopedSize pat + m) -> d) ->
  d
unBindWith (Bind pat r t) f = f pat r t

applyUnder ::
  forall pat v c n1 n2.
  (ScopedSized pat, Subst v v, Subst v c, Subst v pat) =>
  (forall m n. Env v m n -> c m -> c n) ->
  Env v n1 n2 ->
  Bind v c pat n1 ->
  Bind v c pat n2
applyUnder f r2 (Bind p r1 t) =
  Bind p' idE (f r' t)
  where
    r' = upN sp' (r1 .>> r2)
    sp' :: SNat (ScopedSize pat)
    sp' = size p'
    p' :: pat n2
    p' = applyE r2 p

-- Map variable 0 to given value, and shift everything else
-- in the environment
instantiateWeakenEnv ::
  forall p n v c.
  (SubstVar v, Subst v v) =>
  SNat p ->
  SNat n ->
  v (p + n) ->
  Env v (S n) (p + n)
instantiateWeakenEnv p n a =
  a .: shiftNE p

-----------------------------------------------------------------
-- instances for Bind
-----------------------------------------------------------------

instance (ScopedSized pat, Subst v pat, Subst v v) => Shiftable (Bind v c pat) where
  shift = shiftFromApplyE @v

instance (ScopedSized pat, Subst v pat, Subst v v) => Subst v (Bind v c pat) where
  applyE (env1 :: Env v n m) (Bind (pat :: pat n) (env2 :: Env v m1 n) m) =
    Bind (applyE env1 pat) (env2 .>> env1) m

instance
  ( Subst v v,
    Subst v c,
    ScopedSized p,
    FV p,
    FV c
  ) =>
  FV (Bind v c p)
  where
  appearsFree n b =
    let pat = getPat b
     in appearsFree n pat
          || appearsFree (Fin.shiftN (scopedSize pat) n) (getBody b)

instance
  (ScopedSized p, SubstVar v, Subst v v, Subst v c, Strengthen c, Strengthen p) =>
  Strengthen (Bind v c p)
  where
  strengthenRec (k :: SNat k) (m :: SNat m) (n :: SNat n) bnd =
    withSNat (sPlus k (sPlus m n)) $
      unbind bnd $ \(p :: p (k + (m + n))) t' ->
        case ( axiomAssoc @(ScopedSize p) @k @(m + n),
               axiomAssoc @(ScopedSize p) @k @n
             ) of
          (Refl, Refl) ->
            let p' :: Maybe (p (k + n))
                p' = strengthenRec k m n p

                r :: Maybe (c (ScopedSize p + (k + n)))
                r = strengthenRec (sPlus (scopedSize p) k) m n t'
             in bind <$> p' <*> r

-----------------------------------------------------------------
-- Telescopes
---------------------------------------------------------------

-- Telescopes are parameterized by scoped patterns, with kinds
-- `pat :: Nat -> Nat -> Type`. For these types, we need to know
-- that the first argument is the number of binding variables,
-- (i.e. Size or ScopedSize) so we need yet *another* type class
-- to make this constraint.

class (ScopedSize (t p) ~ p) => EqScopedSized t p

instance (ScopedSize (t p) ~ p) => EqScopedSized t p

class
  ( forall p. ScopedSized (pat p),
    forall p. EqScopedSized pat p
  ) =>
  IScopedSized pat

-- with this type class, we wrap the size function yet again
-- to give it an easier to use type
iscopedSize :: (IScopedSized pat) => pat p n -> SNat p
iscopedSize = scopedSize

iscopedNames :: (IScopedSized pat, Named name (pat p n)) => pat p n -> Vec p name
iscopedNames = scopedNames

iscopedData :: forall pat p n u s. (IScopedSized pat, WithData (pat p n) u s n) => pat p n -> DS.Scope u s p n
iscopedData p = get
  where
    get :: (ScopedSize (pat p) ~ p) => DS.Scope u s p n
    get = scopedData @_ @_ @_ @_ @n p

iscopedPatEq ::
  (IScopedSized pat1, IScopedSized pat2, PatEq (pat1 p1 n1) (pat2 p2 n2)) =>
  pat1 p1 n1 ->
  pat2 p2 n2 ->
  Maybe (p1 :~: p2)
iscopedPatEq = scopedPatEq

-- | Telescopes: lists of local assumptions
-- These are scoped patterns because they include terms
-- that can mention variables that are already in scope
-- or that have been bound earlier in the pattern.
-- 'p' is the number of variables introduced by the telescope
-- 'n' is the scope depth for A1 (and A2 has depth S n, etc.)
-- We include the appropriate associativity property with ICons so
-- that it is always available for pattern matching
data TeleList (pat :: Nat -> Nat -> Type) p n where
  TNil :: TeleList pat N0 n
  TCons ::
    ( IScopedSized pat,
      p2 + (p1 + n) ~ (p2 + p1) + n
    ) =>
    pat p1 n ->
    TeleList pat p2 (p1 + n) ->
    TeleList pat (p2 + p1) n

lengthTele :: TeleList pat p n -> Int
lengthTele TNil = 0
lengthTele (TCons _ ps) = 1 + lengthTele ps

-- Smart constructor
(<:>) ::
  forall p1 p2 pat n.
  (IScopedSized pat) =>
  pat p1 n ->
  TeleList pat p2 (p1 + n) ->
  TeleList pat (p2 + p1) n
e <:> t = case axiomAssoc @p2 @p1 @n of Refl -> TCons e t

infixr 9 <:>

instance IScopedSized (TeleList pat)

instance ScopedSized (TeleList pat p) where
  type ScopedSize (TeleList pat p) = p

instance Sized (TeleList pat p n) where
  type Size (TeleList pat p n) = p
  size TNil = s0
  size (TCons p1 p2) = sPlus (size p2) (iscopedSize p1)

instance
  ( forall p1 n. Named name (pat p1 n),
    IScopedSized pat
  ) =>
  Named name (TeleList pat p n)
  where
  names TNil = VNil
  names (TCons p ps) =
    Vec.append (names ps) (iscopedNames p)

instance
  (SubstVar s, forall p1 n. WithData (pat p1 n) u s n, IScopedSized pat) =>
  WithData (TeleList pat p n) u s n
  where
  getData TNil = DS.empty
  getData (TCons (p :: pat p1 n) (ps :: TeleList pat p2 (p1 + n))) =
    let (p2, ps') = getSizeData @_ @_ @_ @(p1 + n) ps
     in withSNat p2 $ DS.append @_ @_ @_ @_ @n (iscopedData p) ps'

instance (IScopedSized pat, Subst v v, forall p. Subst v (pat p)) => Shiftable (TeleList pat p) where
  shift = shiftFromApplyE @v

instance
  (IScopedSized pat, Subst v v, forall p. Subst v (pat p)) =>
  Subst v (TeleList pat p)
  where
  applyE r TNil = TNil
  applyE r (TCons p1 p2) =
    applyE r p1 <:> applyE (upN (iscopedSize p1) r) p2

instance (IScopedSized pat, forall p. FV (pat p)) => FV (TeleList pat p) where
  appearsFree ::
    forall n.
    (IScopedSized pat, forall p1. FV (pat p1)) =>
    Fin n ->
    TeleList pat p n ->
    Bool
  appearsFree n TNil = False
  appearsFree n (TCons p1 p2) = appearsFree n p1 || appearsFree (Fin.shiftN (iscopedSize p1) n) p2

instance (forall p1. Strengthen (pat p1)) => Strengthen (TeleList pat p) where
  strengthenRec k m n TNil = Just TNil
  strengthenRec (k :: SNat k) (m :: SNat m) (n :: SNat n) (TCons (p1 :: pat p1 (k + (m + n))) p2) =
    case ( axiomAssoc @p1 @k @(m + n),
           axiomAssoc @p1 @k @n
         ) of
      (Refl, Refl) ->
        (<:>)
          <$> strengthenRec k m n p1
          <*> strengthenRec (sPlus (iscopedSize p1) k) m n p2

instance
  (forall p1 p2 n1 n2. PatEq (pat p1 n1) (pat p2 n2), IScopedSized pat) =>
  PatEq (TeleList pat p1 n1) (TeleList pat p2 n2)
  where
  patEq TNil TNil = Just Refl
  patEq (TCons p1 p2) (TCons p1' p2')
    | Just Refl <- iscopedPatEq p1 p1',
      Just Refl <- iscopedPatEq p2 p2' =
        Just Refl
  patEq _ _ = Nothing

-----------------------------------------------------------------
-- Rebind
-- TODO: this is the binary version of a telescope.
-- Captures the left-to-right relationship between two patterns
-- without the list.
---------------------------------------------------------------
{-
data Rebind p1 p2 n where
  Rebind ::
    Plus (Size (p2 n)) (Plus (Size (p1 n)) n) ~ Plus (Plus (Size (p2 n)) (Size (p1 n))) n =>
    p1 n -> p2 (Plus (Size (p1 n)) n) -> Rebind p1 p2 n

rebind :: forall p1 p2 n. p1 n -> p2 (Plus (Size (p1 n)) n) -> Rebind p1 p2 n
rebind p1 p2 =
  case axiomAssoc @(Size (p2 n)) @(Size (p1 n)) @n of
    Refl -> Rebind p1 p2

instance (ScopedSized p1, ScopedSized p2) => Sized (Rebind p1 p2 n) where
    type Size (Rebind p1 p2 n) = Plus (Size (p2 n)) (Size (p1 n))
    size (Rebind p1 p2) = sPlus @(Size (p2 n)) @(Size (p1 n)) (size p2) (size p1)

-- instance (Sized p1, Sized p2) => Sized (Rebind p1 p2) where
--  type Size (Rebind p1 p2) = Plus (Size p2) (Size p1)
--  size (Rebind p1 p2) = sPlus (size p2) (size p1)

instance
  (Subst v v, forall n. ScopedSized p1, Subst v p1, Subst v p2) =>
  Subst v (Rebind p1 p2)
  where
  applyE ::
    (Subst v v, ScopedSized p1, Subst v p2) =>
    Env v n m ->
    Rebind p1 p2 n ->
    Rebind p1 p2 m
  applyE r (Rebind p1 p2) =
    rebind (applyE r p1) (applyE (upN (size p1) r) p2)

instance (forall n. ScopedSized p1, FV p2) => FV (Rebind p1 p2) where
  appearsFree :: (ScopedSized p1, FV p2) => Fin n -> Rebind p1 p2 n -> Bool
  appearsFree n (Rebind p1 p2) = appearsFree (shiftN (size p1) n) p2

unRebind ::
  forall p1 p2 n c.
  (ScopedSized p1, ScopedSized p2, SNatI n) =>
  Rebind p1 p2 n ->
  ( ( SNatI (Size (p1 n)),
      SNatI (Size (p2 n)),
      SNatI (Plus (Size (p1 n)) n),
      Plus (Size (p2 n)) (Plus (Size (p1 n)) n) ~ Plus (Plus (Size (p2 n)) (Size (p1 n))) n
    ) =>
    p1 n ->
    p2 (Plus (Size (p1 n)) n) ->
    c
  ) ->
  c
unRebind (Rebind p1 p2) f =
  case axiomAssoc @(Size (p2 n)) @(Size (p1 n)) @n of
    Refl ->
      withSNat (size p1) $
        withSNat (size p2) $
          withSNat (sPlus (size p1) (snat @n)) $
            f p1 p2
-}