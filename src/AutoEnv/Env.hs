{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : AutoEnv.Env
-- Description : Environments
-- Stability   : experimental
module AutoEnv.Env
  ( Env,
    applyEnv,
    SubstVar (..),
    Subst (..),
    Shiftable (..),
    GSubst (..),
    gapplyE,
    applyOpt,
    transform,
    zeroE,
    oneE,
    singletonE,
    idE,
    (.>>),
    (.:),
    (.++),
    head,
    tail,
    appendE,
    up,
    upN,
    shift1E,
    shiftNE,
    fromVec,
    toVec,
    Refinement (..),
    emptyR,
    joinR,
    singletonR,
    fromRefinement,
    toRefinement,
    refine,
    domain,
    tabulate,
    fromTable,
    weakenE',
    weakenER,
    shiftFromApplyE,
  )
where

import AutoEnv.Classes (Shiftable (..))
import AutoEnv.Env.Internal
import AutoEnv.Lib
import Control.Monad
import Data.Fin (Fin (..))
import Data.Fin qualified as Fin
import Data.Map qualified as Map
import Data.Vec qualified as Vec
import GHC.Generics hiding (S)
import Prelude hiding (head, tail)

----------------------------------------------
-- operations on environments/substitutions
----------------------------------------------

-- TODO: do we want to replace uses of this operation with something else?
env :: forall m v n. (SubstVar v, SNatI m) => (Fin m -> v n) -> Env v m n
env f = fromVec v
  where
    v :: Vec m (v n)
    v = Vec.tabulate f

-- | A singleton environment (single index domain)
-- maps that single variable to `v n`
oneE :: (SubstVar v) => v n -> Env v (S Z) n
oneE v = v .: zeroE

-- | an environment that maps index 0 to v and leaves
-- all other indices alone.
singletonE :: (SubstVar v) => v n -> Env v (S n) n
singletonE v = v .: idE

-- | identity environment, any size
idE :: (SubstVar v) => Env v n n
idE = shiftNE s0

-- | append two environments
-- The `SNatI` constraint is a runtime witness for the length
-- of the domain of the first environment. By using a class
-- constraint, this can be an infix operation.
(.++) ::
  (SNatI p, SubstVar v) =>
  Env v p n ->
  Env v m n ->
  Env v (p + m) n
(.++) = appendE snat

-- | append two environments: explicit length `SNat p` required
-- for the domain of the first list
appendE ::
  (SubstVar v) =>
  SNat p ->
  Env v p n ->
  Env v m n ->
  Env v (p + m) n
appendE SZ e1 e2 = e2
appendE (snat_ -> SS_ p1) e1 e2 =
  head e1 .: appendE p1 (tail e1) e2

newtype AppendE v m n p = MkAppendE
  { getAppendE ::
      Env v p n ->
      Env v m n ->
      Env v (p + m) n
  }

-- | access value at index 0
head :: (SubstVar v) => Env v (S n) m -> v m
head f = applyEnv f FZ

-- | increment all free variables by 1
shift1E :: (SubstVar v) => Env v n (S n)
shift1E = shiftNE s1

-- | Shift an environment by size `p`
upN ::
  forall v p m n.
  (Subst v v) =>
  SNat p ->
  Env v m n ->
  Env v (p + m) (p + n)
upN p = getUpN @_ @_ @_ @p (withSNat p (induction base step))
  where
    base :: UpN v m n Z
    base = MkUpN id
    step :: forall p1. UpN v m n p1 -> UpN v m n (S p1)
    step (MkUpN r) = MkUpN $
      \e -> var Fin.f0 .: (r e .>> shiftNE s1)

newtype UpN v m n p = MkUpN {getUpN :: Env v m n -> Env v (p + m) (p + n)}

shiftFromApplyE :: forall v c k n. (SubstVar v, Subst v c) => SNat k -> c n -> c (k + n)
shiftFromApplyE k = applyE @v (shiftNE k)

----------------------------------------------------
-- Create an environment from a length-indexed
-- vector of scoped values

fromVec :: (SubstVar v) => Vec m (v n) -> Env v m n
fromVec VNil = zeroE
fromVec (x ::: vs) = x .: fromVec vs

toVec :: (SubstVar v) => SNat m -> Env v m n -> Vec m (v n)
toVec SZ r = VNil
toVec m@(snat_ -> SS_ m') r = head r ::: toVec m' (tail r)

----------------------------------------------------------------
-- Refinements
----------------------------------------------------------------

-- A refinement is a special kind of substitution that does not
-- change the scope, it just replaces all uses of a particular variable
-- with some other term (which could mention that variable).
newtype Refinement v n = Refinement (Map.Map (Fin n) (v n))

emptyR :: Refinement v n
emptyR = Refinement Map.empty

-- | Note, this operation fails when xs and ys have overlapping domains
joinR ::
  forall v n.
  (SNatI n, Subst v v, Eq (v n)) =>
  Refinement v n ->
  Refinement v n ->
  Maybe (Refinement v n)
joinR (Refinement xs) (Refinement ys) =
  Refinement <$> foldM f ys xs'
  where
    xs' = Map.toList xs
    r = fromTable xs'
    f :: Map.Map (Fin n) (v n) -> (Fin n, v n) -> Maybe (Map.Map (Fin n) (v n))
    f m (k, v)
      | Map.member k ys = Nothing
      | otherwise =
          let v' = applyE r v
           in Just $ if v' == var k then m else Map.insert k (applyE r v) m

singletonR :: (SubstVar v, Eq (v n)) => (Fin n, v n) -> Refinement v n
singletonR (x, t) =
  if t == var x then emptyR else Refinement (Map.singleton x t)

-- Move a refinement to a new scope
instance (Shiftable v) => Shiftable (Refinement v) where
  shift :: forall k n. SNat k -> Refinement v n -> Refinement v (k + n)
  shift k (Refinement (r :: Map.Map (Fin n) (v n))) = Refinement g'
    where
      f' = Map.mapKeysMonotonic (Fin.shiftN @k @n k) r
      g' = Map.map (shift k) f'

fromRefinement :: (SNatI n, SubstVar v) => Refinement v n -> Env v n n
fromRefinement (Refinement x) = fromTable (Map.toList x)

toRefinement :: (SNatI n, SubstVar v) => Env v n n -> Refinement v n
toRefinement r = Refinement (Map.fromList (tabulate r))

refines :: forall n v. (SNatI n, Subst v v, Eq (v n)) => Refinement v n -> Fin n -> Bool
refines r i = applyE (fromRefinement r) (var @v i) /= var @v i

refine :: (SNatI n, Subst v c) => Refinement v n -> c n -> c n
refine r = applyE (fromRefinement r)

domain :: Refinement v n -> [Fin n]
domain (Refinement m) = Map.keys m

----------------------------------------------------------------
-- show for environments
----------------------------------------------------------------

instance (SNatI n, Show (v m), SubstVar v) => Show (Env v n m) where
  show x = show (tabulate x)

tabulate :: (SNatI n, Subst v v) => Env v n m -> [(Fin n, v m)]
tabulate r = map (\f -> (f, applyEnv r f)) Fin.universe

fromTable ::
  forall n v.
  (SNatI n, SubstVar v) =>
  [(Fin n, v n)] ->
  Env v n n
fromTable rho =
  env $ \f -> case lookup f rho of
    Just t -> t
    Nothing -> var f

--------------------------------------------
-- Generic implementation of Subst class
-----------------------------------------------

-- Constant types
instance GSubst v (K1 i c) where
  gsubst s (K1 c) = K1 c
  {-# INLINE gsubst #-}

instance GSubst v U1 where
  gsubst _s U1 = U1
  {-# INLINE gsubst #-}

instance (GSubst b f) => GSubst b (M1 i c f) where
  gsubst s = M1 . gsubst s . unM1
  {-# INLINE gsubst #-}

instance GSubst b V1 where
  gsubst _s = error "BUG: void type"
  {-# INLINE gsubst #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gsubst s (f :*: g) = gsubst s f :*: gsubst s g
  {-# INLINE gsubst #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gsubst s (L1 f) = L1 $ gsubst s f
  gsubst s (R1 g) = R1 $ gsubst s g
  {-# INLINE gsubst #-}

instance (Subst b g) => GSubst b (Rec1 g) where
  gsubst s (Rec1 f) = Rec1 (applyE s f)

instance Shiftable Fin where
  shift = Fin.shiftN

instance SubstVar Fin where
  var x = x

instance {-# OVERLAPS #-} Subst Fin Fin where
  applyE = applyEnv

instance {-# OVERLAPPABLE #-} (SubstVar v) => Subst v Fin where
  applyE = error "BUG: this case is impossible"

instance GSubst b Fin where
  gsubst s f = error "BUG: add a Var case to your definition of applyE"
