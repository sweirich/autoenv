module AutoEnv.Context where

import AutoEnv.Classes
import AutoEnv.Env
import AutoEnv.Lib

----------------------------------------------------------------
-- For dependently-typed languages
----------------------------------------------------------------

type Ctx v n = Env v n n

-- This is not weakening --- it increments all variables by one
shiftC :: forall v n. (SubstVar v) => v n -> v (S n)
shiftC = applyE @v shift1E

shiftCtx :: (SubstVar v) => Env v n n -> Env v n (S n)
shiftCtx g = g .>> shift1E

-- | An empty context, that includes no variable assumptions
emptyC :: Ctx v N0
emptyC = zeroE

-- | Append a new definition to the context
-- All existing types in the context need to be shifted (lazily)
(+++) :: forall v n. (SubstVar v) => Ctx v n -> v n -> Ctx v (S n)
g +++ a = applyE @v shift1E a .: (g .>> shift1E)

{-
data Exp n = Star | Var (Fin n) deriving Show
instance SubstVar Exp where var = Var
instance Subst Exp Exp where
    applyE s Star = Star
    applyE s (Var x) = applyEnv s x


-- c :: Ctx Exp N4
-- x : * , y : x, z : x , w : *
c = emptyC +++ Star +++ Var FZ +++ Var (FS FZ) +++ Star

f0 :: Fin (S N3)
f0 = FZ

f1 :: Fin (S N3)
f1 = FS FZ

f2 :: Fin (S N3)
f2 = FS (FS FZ)

f3 :: Fin (S (S (S (S n1))))
f3 = FS (FS (FS FZ))

-- >>> applyEnv c f1
-- Var 3
-}

(++++) :: forall v n n' m. (SNatI n', SubstVar v) => Env v n m -> Env v n' (n' + m) -> Env v (n' + n) (n' + m)
l ++++ r =
  let p = snat @n'
   in r .++ (l .>> shiftNE p)