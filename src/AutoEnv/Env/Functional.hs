{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
module AutoEnv.Env.Functional where

-- Represents the environment using a function


import AutoEnv.Lib
import Data.Fin (Fin(..))
import qualified Data.Fin as Fin
import qualified Data.Fin as Fin
import GHC.Generics hiding (S)

------------------------------------------------------------------------------
-- Substitution class declarations
------------------------------------------------------------------------------
-- | Well-scoped types that can be the range of
-- an environment. This should generally be the `Var`
-- constructor from the syntax.
class (Subst v v) => SubstVar (v :: Nat -> Type) where
  var :: Fin n -> v n

-- | Apply the environment throughout a term of
-- type `c n`, replacing variables with values
-- of type `v m`
class (SubstVar v) => Subst v c where
  applyE :: Env v n m -> c n -> c m
  default applyE :: (Generic1 c, GSubst v (Rep1 c), SubstVar v) => Env v m n -> c m -> c n
  applyE = gapplyE
  {-# INLINE applyE #-}

-- Generic programming
class GSubst v (e :: Nat -> Type) where
  gsubst :: Env v m n -> e m -> e n

gapplyE :: (Generic1 c, GSubst v (Rep1 c), SubstVar v) => Env v m n -> c m -> c n
gapplyE = applyOpt (\s x -> to1 $ gsubst s (from1 x))
{-# INLINEABLE gapplyE #-}

------------------------------------------------------------------------------
-- Environment representation as finite function
------------------------------------------------------------------------------

newtype Env (a :: Nat -> Type) (n :: Nat) (m :: Nat) =
    Env { applyEnv :: Fin n -> a m }

------------------------------------------------------------------------------
-- Application
------------------------------------------------------------------------------

-- | Value of the index x in the substitution s
-- applyEnv :: (SubstVar a) => Env a n m -> Fin n -> a m
-- applyEnv f = f
-- {-# INLINEABLE applyEnv #-}

-- | Build an optimized version of applyE (does nothing here)
applyOpt :: (Env v n m -> c n -> c m) -> (Env v n m -> c n -> c m)
applyOpt f = f
{-# INLINEABLE applyOpt #-}

------------------------------------------------------------------------------
-- Construction and modification
------------------------------------------------------------------------------

-- | The empty environment (zero domain)
zeroE :: Env v Z n
zeroE = Env $ \ x -> case x of {}
{-# INLINEABLE zeroE #-}

-- make the bound bigger, on the right, but do not change any indices.
-- this is an identity function
weakenER :: forall m v n. (SubstVar v) => SNat m -> Env v n (n + m)
weakenER m = Env $ \x -> var (Fin.weakenFinRight m x)
{-# INLINEABLE weakenER #-}

-- make the bound bigger, on the left, but do not change any indices.
-- this is an identity function
weakenE' :: forall m v n. (SubstVar v) => SNat m -> Env v n (m + n)
weakenE' m = Env $ \x -> var (Fin.weakenFin m x)
{-# INLINEABLE weakenE' #-}

-- | increment all free variables by m
shiftNE :: (SubstVar v) => SNat m -> Env v n (m + n)
shiftNE m = Env $ \x -> var (Fin.shiftN m x)
{-# INLINEABLE shiftNE #-}

-- | `cons` -- extend an environment with a new mapping
-- for index '0'. All existing mappings are shifted over.
(.:) :: SubstVar v => v m -> Env v n m -> Env v (S n) m
ty .: s = Env $ \y -> case y of
                 FZ -> ty
                 FS x -> applyEnv s x
{-# INLINEABLE (.:) #-}

-- | inverse of `cons` -- remove the first mapping
tail :: (SubstVar v) => Env v (S n) m -> Env v n m
tail x = shiftNE s1 .>> x
{-# INLINEABLE tail #-}

-- | composition: do f then g
(.>>) :: (Subst v v) => Env v p n -> Env v n m -> Env v p m
(.>>) = comp
{-# INLINEABLE (.>>) #-}

-- | smart constructor for composition
comp :: forall a m n p. SubstVar a =>
         Env a m n -> Env a n p -> Env a m p
comp s1 s2 = Env $ \x -> applyE s2 (applyEnv s1 x)
{-# INLINEABLE comp #-}

-- | modify an environment so that it can go under a binder
up :: (SubstVar v) => Env v m n -> Env v (S m) (S n)
up e = var Fin.f0 .: comp e (shiftNE s1)
{-# INLINEABLE up #-}

-- | mapping operation for range of the environment
transform :: (forall m. a m -> b m) -> Env a n m -> Env b n m
transform f g = Env $ \x -> f (applyEnv g x)
{-# INLINEABLE transform #-}
