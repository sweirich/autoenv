module AutoEnv.Scope
  ( Scope (..),
    empty,
    singleton,
    append',
    append,
    nth,
    transform,
  )
where

import AutoEnv.Env hiding (transform)
import AutoEnv.Env qualified as Env
import AutoEnv.Context
import Data.Fin
import Data.SNat
import Data.Type.Equality
import Data.Vec (Vec)
import Data.Vec qualified as Vec

-- Note that we could parametrize all subsequent definitions by an initial
-- scope. We instead make the choice of fixing the outer scope to Z. This
-- simplifies all subsequent definition, and working in a latent undefined scope
-- seems exotic and can be emulated fairly easily.
data Scope u s p n = Scope {uscope :: Vec p u, sscope :: Env s p (p + n)}

empty :: Scope u s Z n
empty = Scope Vec.empty zeroE

singleton :: forall u s n. (SubstVar s) => u -> s n -> Scope u s N1 n
singleton = singleton' @s
  where
    singleton' :: forall v u s n. (Subst s s) => u -> s n -> Scope u s N1 n
    singleton' u v = let v' = applyE (shift1E @s) v in Scope (Vec.singleton u) (oneE @s @(S n) v')

append' :: forall n u s pl pr. (SubstVar s, SNatI pr) => Scope u s pl n -> Scope u s pr (pl + n) -> Scope u s (pr + pl) n
append' (Scope ul sl) (Scope ur sr) = case axiomAssoc @pr @pl @n of Refl -> Scope (Vec.append ur ul) (sl ++++ sr)

append :: forall n u s pl pr. (SubstVar s) => Scope u s pl n -> Scope u s pr (pl + n) -> Scope u s (pr + pl) n
append l r@(Scope ur _) = withSNat (Vec.vlength ur) $ append' @n @u @s @pl @pr l r

nth :: (SubstVar s) => Fin p -> Scope u s p n -> (u, s (p + n))
nth i (Scope u s) = (u Vec.! i, s `applyEnv` i)

transform :: (u -> u') -> (forall m. s m -> s' m) -> Scope u s p n -> Scope u' s' p n
transform f g (Scope u s) = Scope (Vec.map f u) (Env.transform g s)
