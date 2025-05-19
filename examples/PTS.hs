-- Pure-type system-like example
-- Includes Pi/Sigma, untyped equivalence
module PTS where

import AutoEnv

import qualified AutoEnv.Bind.Pat as Pat
import AutoEnv.Bind.PatN as PatN
import AutoEnv.Context
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Data.Fin(Fin(..), f0,f1,f2)
import Data.Fin qualified as Fin
import Data.Vec qualified as Vec

-- In a pure type system, terms and types are combined
-- into the same syntactic class.

data Exp (n :: Nat) where
  -- | sort
  Star :: Exp n
  -- | dependent type `Pi x : A . B`
  Pi :: Exp n -> Bind1 Exp Exp n -> Exp n
  -- | variable
  Var :: Fin n -> Exp n
  -- | lambda expression, with type annotation  `lambda x:A.B`
  Lam :: Exp n -> Bind1 Exp Exp n -> Exp n
  -- | application
  App :: Exp n -> Exp n -> Exp n
  -- | dependent pair `Sigma x:A . B`
  Sigma :: Exp n -> Bind1 Exp Exp n -> Exp n
  -- | construct a pair, third argument is type annotation
  Pair :: Exp n -> Exp n -> Exp n -> Exp n
  -- | elimination form for pairs. `split e1 as (x,y) in e2`
  -- Binds two variables to
  -- the two components of the pair
  Split :: Exp n -> Bind2 Exp Exp n -> Exp n

----------------------------------------------

instance SubstVar Exp where
  var :: Fin n -> Exp n
  var = Var

instance Shiftable Exp where
  shift = shiftFromApplyE @Exp

instance Subst Exp Exp where
  applyE :: Env Exp n m -> Exp n -> Exp m
  applyE r Star = Star
  applyE r (Pi a b) = Pi (applyE r a) (applyE r b)
  applyE r (Var x) = applyEnv r x
  applyE r (Lam a b) = Lam (applyE r a) (applyE r b)
  applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
  applyE r (Sigma a b) = Sigma (applyE r a) (applyE r b)
  applyE r (Pair e1 e2 t1) = Pair (applyE r e1) (applyE r e2) (applyE r t1)
  applyE r (Split e1 e2) = Split (applyE r e1) (applyE r e2)

----------------------------------------------

t00 :: Exp N2
t00 = App (Var f0) (Var f0)

t01 :: Exp N2
t01 = App (Var f0) (Var f1)

-- Does a variable appear free in a term?

-- >>> appearsFree f0 t00
-- True

-- >>> appearsFree f1 t00
-- False
instance FV Exp where
  appearsFree :: Fin n -> Exp n -> Bool
  appearsFree n (Var x) = n == x
  appearsFree n Star = False
  appearsFree n (Pi a b) = appearsFree n a || appearsFree (FS n) (getBody1 b)
  appearsFree n (Lam a b) = appearsFree n a || appearsFree (FS n) (getBody1 b)
  appearsFree n (App a b) = appearsFree n a || appearsFree n b
  appearsFree n (Sigma a b) = appearsFree n a || appearsFree (FS n) (getBody1 b)
  appearsFree n (Pair a b t) = appearsFree n a || appearsFree n b || appearsFree n t
  appearsFree n (Split a b) = appearsFree n a || appearsFree (FS (FS n)) (getBody2 b)

-- >>> :t weaken' s1 t00
-- weaken' s1 t00 :: Exp ('S ('S N1))

-- >>> weaken' s1 t00
-- 0 0

weaken' :: SNat m -> Exp n -> Exp (m + n)
weaken' m = applyE @Exp (weakenE' m)

-- >>> strengthen' s1 s1 t00
-- Just (0 0)

-- >>> strengthen' s1 s1 t01
-- Nothing

instance Strengthen Exp where

  strengthenRec k m n (Var x) = Var <$> strengthenRec k m n x
  strengthenRec k m n Star = pure Star
  strengthenRec k m n (Pi a b) = Pi <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (Lam a b) = Lam <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (App a b) = App <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (Sigma a b) = Sigma <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (Pair a b t) = Pair <$> strengthenRec k m n a <*> strengthenRec k m n b <*> strengthenRec k m n t
  strengthenRec k m n (Split a b) = Split <$> strengthenRec k m n a <*> strengthenRec k m n b

----------------------------------------------
-- Examples

-- The identity function "λ x. x". With de Bruijn indices
-- we write it as "λ. 0"
t0 :: Exp Z
t0 = Lam Star (bind1 (Var f0))

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
t1 =
  Lam
    Star
    ( bind1
        ( Lam
            Star
            ( bind1
                ( Var f1
                    `App` (Lam Star (bind1 (Var f0)) `App` Var f0)
                )
            )
        )
    )

-- To show lambda terms, we can write a simple recursive instance of
-- Haskell's `Show` type class. In the case of a binder, we use the `unbind1`
-- operation to access the body of the lambda expression.

-- >>> t0
-- λ. 0

-- >>> t1
-- λ. λ. 1 (λ. 0 0)

-- Polymorphic identity function and its type

tyid = Pi Star (bind1 (Pi (Var f0) (bind1 (Var f1))))

tmid = Lam Star (bind1 (Lam (Var f0) (bind1 (Var f0))))

-- >>> tyid
-- Pi *. 0 -> 1

-- >>> tmid
-- λ. λ. 0

instance Show (Exp n) where
  showsPrec :: Int -> Exp n -> String -> String
  showsPrec _ Star = showString "*"
  showsPrec d (Pi a b)
    | appearsFree FZ (getBody1 b) =
        showParen (d > 10) $
          showString "Pi "
            . shows a
            . showString ". "
            . shows (getBody1 b)
    | otherwise =
        showParen (d > 10) $
          showsPrec 11 a
            . showString " -> "
            . showsPrec 10 (getBody1 b)
  showsPrec d (Sigma a b)
    | appearsFree FZ (getBody1 b) =
        showParen (d > 10) $
          showString "Sigma "
            . shows a
            . showString ". "
            . shows (getBody1 b)
    | otherwise =
        showParen (d > 10) $
          showsPrec 11 a
            . showString " * "
            . showsPrec 10 (getBody1 b)
  showsPrec _ (Var x) = shows x
  showsPrec d (App e1 e2) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString " "
        . showsPrec 11 e2
  showsPrec d (Lam t b) =
    showParen (d > 10) $
      showString "λ. "
        . shows (getBody1 b)
  showsPrec d (Pair e1 e2 t) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString ", "
        . showsPrec 11 e2
  showsPrec d (Split t b) =
    showParen (d > 10) $
      showString "split"
        . showsPrec 10 t
        . showString " in "
        . shows (getBody2 b)

-- To compare binders, we only need to `getBody1` them
instance (Eq (Exp n)) => Eq (Bind1 Exp Exp n) where
  b1 == b2 = getBody1 b1 == getBody1 b2

-- This is also true for double binders
instance (Eq (Exp n)) => Eq (Bind2 Exp Exp n) where
  b1 == b2 = getBody2 b1 == getBody2 b2

-- With the instance above the derivable equality instance
-- is alpha-equivalence
deriving instance (Eq (Exp n))

--------------------------------------------------------

{- We can write the usual operations for evaluating
   lambda terms to values -}

-- big-step evaluation

-- >>> eval t1
-- λ. λ. 1 (λ. 0 0)

-- >>> eval (t1 `App` t0)
-- λ. λ. 0 (λ. 0 0)

eval :: Exp n -> Exp n
eval (Var x) = Var x
eval (Lam a b) = Lam a b
eval (App e1 e2) =
  let v = eval e2
   in case eval e1 of
        Lam a b -> eval (instantiate1 b v)
        t -> App t v
eval Star = Star
eval (Pi a b) = Pi a b
eval (Sigma a b) = Sigma a b
eval (Pair a b t) = Pair a b t
eval (Split a b) =
  case eval a of
    Pair a1 a2 _ ->
      eval (instantiate2 b (eval a1) (eval a2))
    t -> Split t b

-- small-step evaluation

-- >>> step (t1 `App` t0)
-- Just (λ. λ. 0 (λ. 0 0))

step :: Exp n -> Maybe (Exp n)
step (Var x) = Nothing
step (Lam a b) = Nothing
step (App (Lam a b) e2) = Just (instantiate1 b e2)
step (App e1 e2)
  | Just e1' <- step e1 = Just (App e1' e2)
  | Just e2' <- step e2 = Just (App e1 e2')
  | otherwise = Nothing
step Star = Nothing
step (Pi a b) = Nothing
step (Sigma a b) = Nothing
step (Pair a b _) = Nothing
step (Split (Pair a1 a2 _) b) = Just (PatN.instantiate2 b a1 a2)
step (Split a b)
  | Just a' <- step a = Just (Split a' b)
  | otherwise = Nothing

eval' :: Exp n -> Exp n
eval' e
  | Just e' <- step e = eval' e'
  | otherwise = e

-- normalization
-- to normalize under a lambda expression, we must first unbind
-- it and then rebind it when finished

-- >>> nf t1
-- λ. λ. 1 0

-- >>> nf (t1 `App` t0)
-- λ. λ. 0 0

-- reduce the term everywhere, as much as possible
nf :: Exp n -> Exp n
nf (Var x) = Var x
nf (Lam a b) = Lam a (bind1 (nf (getBody1 b)))
nf (App e1 e2) =
  case nf e1 of
    Lam a b -> nf (instantiate1 b e2)
    t -> App t (nf e2)
nf Star = Star
nf (Pi a b) = Pi (nf a) (bind1 (nf (getBody1 b)))
nf (Sigma a b) = Sigma (nf a) (bind1 (nf (getBody1 b)))
nf (Pair a b t) = Pair (nf a) (nf b) (nf t)
nf (Split a b) =
  case nf a of
    Pair a1 a2 _ -> nf (PatN.instantiate2 b a1 a2)
    t -> Split t (PatN.bind2 (nf (getBody2 b)))

-- first find the head form
whnf :: Exp n -> Exp n
whnf (App a1 a2) = case whnf a1 of
  Lam a b -> whnf (instantiate1 b a1)
  t -> App t a2
whnf (Split a b) = case whnf a of
  Pair a1 a2 _ -> whnf (PatN.instantiate2 b a1 a2)
  t -> Split t b
-- all other terms are already in head form
whnf a = a

norm :: Exp n -> Exp n
norm a = case whnf a of
  Lam a b -> Lam (norm a) (bind1 (norm (getBody1 b)))
  Pi a b -> Pi (norm a) (bind1 (norm (getBody1 b)))
  Sigma a b -> Sigma (norm a) (bind1 (norm (getBody1 b)))
  Pair a b t -> Pair (norm a) (norm b) (norm t)
  Star -> Star
  App a b -> App a (norm b)
  Split a b -> Split a (PatN.bind2 (norm (getBody2 b)))
  Var x -> Var x

--------------------------------------------------------
-- We can also write functions that manipulate the
-- environment explicitly

-- >>> evalEnv idE t1
-- λ. λ. 1 (λ. 0 0)

-- Below, if n is 0, then this function acts like an
-- "environment-based" bigstep evaluator. The result of
-- evaluating a lambda expression is a closure --- the body
-- of the lambda paired with its environment. That is exactly
-- what the implementation of bind1 does.

-- In the case of beta-reduction, the `unBindWith` operation
-- applies its argument to the environment and subterm in the
-- closure. In other words, this function calls `evalEnv`
-- recursively with the saved environment and body of the lambda term.

evalEnv :: Env Exp m n -> Exp m -> Exp n
evalEnv r (Var x) = applyEnv r x
evalEnv r (Lam a b) = applyE r (Lam a b)
evalEnv r (App e1 e2) =
  let v = evalEnv r e2
   in case evalEnv r e1 of
        Lam a b ->
          unbindWith1 b (\r' e' -> evalEnv (v .: r') e')
        t -> App t v
evalEnv r Star = Star
evalEnv r (Pi a b) = applyE r (Pi a b)
evalEnv r (Sigma a b) = applyE r (Sigma a b)
evalEnv r (Pair a b t) = applyE r (Pair a b t)
evalEnv r (Split a b) =
  case evalEnv r a of
    Pair a1 a2 _ ->
      PatN.unbindWith2 b ( \r' e' -> evalEnv (a1 .: (a2 .: (r' .>> r))) e')
    t -> Split t (applyE r b)

----------------------------------------------------------------
data Err where
  Equate :: Exp n -> Exp n -> Err
  PiExpected :: Exp n -> Err
  SigmaExpected :: Exp n -> Err
  VarEscapes :: Exp n -> Err

deriving instance (Show Err)

equate :: (MonadError Err m) => Exp n -> Exp n -> m ()
equate t1 t2 = do
  let n1 = whnf t1
      n2 = whnf t2
  equateWHNF n1 n2

equateWHNF :: (MonadError Err m) => Exp n -> Exp n -> m ()
equateWHNF n1 n2 =
  case (n1, n2) of
    (Star, Star) -> pure ()
    (Var x, Var y) | x == y -> pure ()
    (Lam _ b1, Lam _ b2) -> equate (getBody1 b1) (getBody1 b2)
    (App a1 a2, App b1 b2) -> do
      equateWHNF a1 b1
      equate a2 b2
    (Pi tyA1 b1, Pi tyA2 b2) -> do
      equate tyA1 tyA2
      equate (getBody1 b1) (getBody1 b2)
    (Pair a1 a2 _, Pair b1 b2 _) -> do
      equate a1 b1
      equate a2 b2
    (Split a1 b1, Split a2 b2) -> do
      equateWHNF a1 a2
      equate (getBody2 b1) (getBody2 b2)
    (Sigma tyA1 b1, Sigma tyA2 b2) -> do
      equate tyA1 tyA2
      equate (getBody1 b1) (getBody1 b2)
    (_, _) -> throwError (Equate n1 n2)

----------------------------------------------------------------

checkType ::
  forall n m.
  (MonadError Err m, SNatI n) =>
  Ctx Exp n ->
  Exp n ->
  Exp n ->
  m ()
checkType g e t1 = do
  t2 <- inferType g e
  equate (whnf t2) t1

inferType ::
  forall n m.
  (MonadError Err m, SNatI n) =>
  Ctx Exp n ->
  Exp n ->
  m (Exp n)
inferType g (Var x) = pure (applyEnv g x)
inferType g Star = pure Star
inferType g (Pi a b) = do
  checkType g a Star
  checkType (g +++ a) (getBody1 b) Star
  pure Star
inferType g (Lam tyA b) = do
  checkType g tyA Star
  tyB <- inferType (g +++ tyA) (getBody1 b)
  return $ Pi tyA (bind1 tyB)
inferType g (App a b) = do
  tyA <- inferType g a
  case whnf tyA of
    Pi tyA1 tyB1 -> do
      checkType g b tyA1
      pure $ instantiate1 tyB1 b
    t -> throwError (PiExpected t)
inferType g (Sigma a b) = do
  checkType g a Star
  checkType (g +++ a) (getBody1 b) Star
  pure Star
inferType g (Pair a b ty) = do
  tyA <- inferType g a
  tyB <- inferType g b
  case ty of
    (Sigma tyA tyB) -> do
      checkType g a tyA
      checkType g b (instantiate1 tyB a)
      pure ty
    _ -> throwError (SigmaExpected ty)
inferType g (Split a b) = do
  tyA <- inferType g a
  case whnf tyA of
    Sigma tyA' tyB' -> do
      let g' :: Ctx Exp (S (S n))
          g' = g +++ tyA' +++ getBody1 tyB'
      ty <- inferType g' (getBody2 b)
      let ty' = whnf ty
      case strengthenN s2 ty' of
        Nothing -> throwError (VarEscapes ty)
        Just ty'' -> pure ty''
    _ -> throwError (SigmaExpected tyA)


-- >>> inferType zeroE tmid :: Either Err (Exp N0)
-- Right (Pi *. 0 -> 1)

-- >>> inferType zeroE (App tmid tyid) :: Either Err (Exp N0)
-- Right ((Pi *. 0 -> 1) -> Pi *. 0 -> 1)
