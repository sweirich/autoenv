-- |
-- Module      : NBE
-- Description : Normalization-by-evaluation
--
-- NBE is a technique for normalizing lambda-calculus terms. It involves
-- reifying syntactic terms to another model, evaluating in that model, and
-- then reflecting

-- TODO: This example is incomplete

module NBE where

import AutoEnv
import AutoEnv.Env
import Data.Fin
import AutoEnv.Bind.Single

-- we use the lambda calculus implementation as is
import LC hiding (eval)

-- Inspired by https://github.com/AndrasKovacs/elaboration-zoo/blob/master/01-eval-closures-debruijn/Main.hs
-- Dependent types added by SCW

-- A value is either a closure (i.e. delayed substitution for values)
-- or a path headed by a variable represented by a deBruijn *level*
-- levels count in the opposite direction from indices. This means that
-- the context can be weakened without changing terms.
-- Note that there is no binding form for levels in this AST. The
-- closure case binds a de Bruijn *index* in the value.
data Val m
 = VVar (Fin m)
 | VApp (Val m) (Val m)
 | VLam (Bind Val Exp m)

-- The body of `VLam` is an expression that is closed with respect to
-- indices by the delayed environment in the binder. The `Val`ues in the
-- co-domain of the environment have free levels, bounded by `m`.

instance SubstVar Val where var = VVar

instance Shiftable Val where shift = shiftFromApplyE @Val

instance Subst Val Val where
  applyE r (VVar x) = applyEnv r x
  applyE r (VApp a b) = VApp (applyE r a) (applyE r b)
  applyE r (VLam b) = VLam (applyE r b)

--- TODO apply a function to a saved environment
applyBind :: (v1 n -> v2 m) -> Bind v1 e n -> Bind v2 e m
applyBind f b = undefined
-- applyBind f (Bind (Env r) t) = Bind (Env (f . r)) t

-- weaken the levels in a `Val`. This only makes the scope larger, it does not
-- shift the index. It is an identity function.
weaken1Val :: Val m -> Val (S m)
weaken1Val = applyE @Val (weakenE' s1)

-- A value environment replaces de Bruijn indices with leveled values
type VEnv n m = Env Val n m

--evalInEnv :: Env Val n m -> Bind Exp Exp n -> Bind Val Exp m
-- evalInEnv r b = bind (applyE (up r) (unbind b))

-- Convert an expression to a value
eval :: forall n m. Env Val n m -> Exp n -> Val m
eval r = \case
  Var x -> applyEnv r x
  Lam b -> VLam (applyBind (eval r) b)
  App a1 a2 ->
   let a2' = eval r a2 in
   case eval r a1 of
      (VLam b) -> instantiateWith b a2' eval
      a1' -> VApp a1' a2'

-- | Convert a value to a term by translating
-- all level-based vars to index-based vars
-- l is the current scoping depth, needed for the variable case
-- and for introducing the new bound variable.
quote :: forall l. SNat l -> Val l -> Exp l
quote l = \case
   VVar x   -> withSNat l $ Var (invert x)
   VApp t u -> App (quote l t) (quote l u)
   VLam b ->
       Lam (bind (quote (AutoEnv.succ l)
              (instantiateWith (applyBind weaken1Val b) (withSNat l $ var maxBound) eval)))

vApp :: Bind Val Exp n -> Val n -> Val n
vApp b v = instantiateWith b v eval


-- normalize by reflecting to one domain then
-- reifying the result back
nbe :: Exp N0 -> Exp N0
nbe t = quote s0 (eval zeroE t)