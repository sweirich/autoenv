module Data.Scoped.Telescope where

import AutoEnv.Classes
import AutoEnv.Env (Shiftable (..))
import Data.Fin (Fin)
import Data.Nat
import Data.Type.Equality ((:~:) (..))
import Data.Type.Nat
import Data.Vec.Lazy qualified as Vec
import AutoEnv.Lib (axiomAssoc, axiomPlusZ, axiomSus)
import Data.SNat

-- | Unlike 'Scoped.TeleList', this datatype does not nest: it is effectively a
-- 'List'/'Vec' but with extra scoping inside.
data Telescope u s n m where
  TNil :: Telescope u s Z m
  TCons :: (u, s (n + m)) -> !(Telescope u s n m) -> Telescope u s (S n) m

tmap :: (forall k. u -> s k -> (u', s' k)) -> Telescope u s n m -> Telescope u' s' n m
tmap f TNil = TNil
tmap f (TCons (u, s) xs) = TCons (f u s) (tmap f xs)

empty :: Telescope u s Z m
empty = TNil

singleton :: (u, s n) -> Telescope u s (S Z) n
singleton h = TCons h TNil

append :: forall u s nl nr m. Telescope u s nl (nr + m) -> Telescope u s nr m -> (SNat nl, Telescope u s (nl + nr) m)
append TNil r = (SZ, r)
append (TCons l ls) r =
  case axiomAssoc @nl @nr @m of
    Refl -> let (k, ls') = append ls r in withSNat k (SS, TCons l ls')

toTelescope :: forall p n u s. (Shiftable s) => Vec.Vec p (u, s n) -> Telescope u s p n
toTelescope = snd . iter
  where
    iter :: forall p. Vec.Vec p (u, s n) -> (SNat p, Telescope u s p n)
    iter Vec.VNil = (SZ, TNil)
    iter ((Vec.:::) @_ @p' (u, s) xs) =
      let (sp', sc') :: (SNat p', Telescope u s p' n) = iter xs
          s' :: s (p' + n) = shift sp' s
       in (withSNat sp' SS, TCons (u, s') sc')

fromTelescope :: forall s u p n. (Shiftable s) => Telescope u s p n -> (SNat p, Vec.Vec p (u, s (p + n)))
fromTelescope = iter SZ
  where
    iter :: forall u s k n m. (Shiftable s) => SNat k -> Telescope u s n m -> (SNat (k + n), Vec.Vec n (u, s (k + n + m)))
    iter sk TNil = case axiomPlusZ @k of Refl -> (sk, Vec.empty)
    iter sk (TCons @_ @_ @n' (u, s) sc) =
      case axiomSus @k @n' of
        Refl ->
          let x' :: (u, s (k + n + m)) = case axiomAssoc @k @n' @m of Refl -> (u, shift (addOne sk) s)
              (sn', sc') :: (SNat (k + n), Vec.Vec n' (u, s (k + n + m))) = iter (addOne sk) sc
           in (sn', x' Vec.::: sc')

    addOne :: SNat k -> SNat (S k)
    addOne k = withSNat k SS

emptyTelescope = TNil

nth :: forall s n m u. (Shiftable s) => Fin n -> Telescope u s n m -> (u, s (n + m))
nth i s = snd (fromTelescope s) Vec.! i

instance Sized (Telescope u s n m) where
  type Size (Telescope u s n m) = n
  size :: Telescope u s n m -> SNat n
  size TNil = s0
  size (TCons _ t) = withSNat (size t) SS