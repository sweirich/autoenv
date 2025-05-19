-- |
-- Module      : LC
-- Description : Untyped lambda calculus
-- Stability   : experimental
--
-- An implementation of the untyped lambda calculus including let, letrec,
-- and let* expressions. These examples only use single binding
-- to implement these constructs.
module LCLet where

import AutoEnv
import AutoEnv.Bind.Single
import Data.Fin
import Data.Vec qualified as Vec

-- | Datatype of well-scoped lambda-calculus expressions
data Exp (n :: Nat) where
  Var :: Fin n -> Exp n
  Lam :: Bind Exp Exp n -> Exp n
  App :: Exp n -> Exp n -> Exp n
  Let ::
    -- | single let expression
    -- "let x = e1 in e2" where x is bound in e2
    Exp n ->
    (Bind Exp Exp n) ->
    Exp n
  LetRec ::
    -- | "let rec x = e1 in e2" where x is bound in both e1 and e2
    Bind Exp Exp n ->
    Bind Exp Exp n ->
    Exp n
  LetTele ::
    -- | sequence of nested lets, where each one may depend on
    -- the previous binding
    -- "let x1 = e1 in x2 = e2 in ... in e" where x1 is bound
    -- in e2, e3 ... and e, x2 is bound in e3 and e, etc.
    Tele n ->
    Exp n

data Tele n where
  Body :: Exp n -> Tele n
  LetStar :: Exp n -> Bind Exp Tele n -> Tele n

----------------------------------------------
-- Example lambda-calculus expressions
----------------------------------------------

-- | The identity function "λ x. x".
-- With de Bruijn indices we write it as "λ. 0"
-- The `bind` function creates the binder
-- t0 :: Exp Z
t0 = Lam (bind (Var f0))

-- | A larger term "λ x. λy. x ((λ z. z) y)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
t1 =
  Lam
    ( bind
        ( Lam
            ( bind
                ( Var f1
                    `App` (Lam (bind (Var f0)) `App` Var f0)
                )
            )
        )
    )

-- >>> t0
-- (λ. 0)

-- >>> t1
-- (λ. (λ. (1 ((λ. 0) 0))))

-- let x = \y.y in x x
t2 :: Exp Z
t2 = Let t0 (bind (App (Var f0) (Var f0)))

-- >>> t2
-- (let (λ. 0) in (0 0))

-- let rec fix = \f. f (fix f) in f
t3 = LetRec (bind (Lam (bind (App (Var f0) (App (Var f1) (Var f0)))))) (bind (Var f0))

-- >>> t3
-- (let rec (λ. (0 (1 0))) in 0)

-- let* x1 = \x.x ; x2 = x1 x1 ; x3 = x2 s1 in x3 x2 x1
t4 =
  LetTele
    ( LetStar
        t0
        ( bind
            ( LetStar
                (App (Var f0) (Var f0))
                ( bind
                    ( LetStar
                        (App (Var f0) (Var f1))
                        ( bind
                            (Body (App (App (Var f0) (Var f1)) (Var f2)))
                        )
                    )
                )
            )
        )
    )

-- >>> t4
-- <let-tele>

----------------------------------------------
-- (Alpha-)Equivalence
----------------------------------------------

-- | To compare binders, we need to `getBody` them
-- The `getBody` operation has type
-- `Bind Exp Exp n -> Exp (S n)`
-- as the body of the binder has one more free variable
instance (Subst Exp t, Eq (t (S n))) => Eq (Bind Exp t n) where
  b1 == b2 = getBody b1 == getBody b2

-- | The derivable equality instance
-- is alpha-equivalence
deriving instance (Eq (Exp n))

deriving instance (Eq (Tele n))

----------------------------------------------
-- Substitution
----------------------------------------------

-- To work with this library, we need two type class instances.

-- | Tell the library how to construct variables in the expression
-- type. This class is necessary to construct an indentity
-- substitution---one that maps each variable to itself.
instance SubstVar Exp where
  var :: Fin n -> Exp n
  var = Var

-- The library represents a substitution using an "Environment".
-- The type `Env Exp n m` is a substitution that can be applied to
-- indices bounded by n. It produces a result `Exp` with indices
-- bounded by m. The function `applyEnv` looks up a mapping in
-- an environment.

-- | The operation `applyE` applies an environment
-- (explicit substitution) to an expression.
--
-- The implementation of this operation applies the environment to
-- variable index in the variable case. All other caseas follow
-- via recursion. The library includes a type class instance for
-- the Bind type which handles the variable lifting needed under
-- the binder.
instance Shiftable Exp where
  shift = shiftFromApplyE @Exp
instance Subst Exp Exp where
  applyE :: Env Exp n m -> Exp n -> Exp m
  applyE r (Var x) = applyEnv r x
  applyE r (Lam b) = Lam (applyE r b)
  applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
  applyE r (Let e1 e2) = Let (applyE r e1) (applyE r e2)
  applyE r (LetRec e1 e2) = LetRec (applyE r e1) (applyE r e2)
  applyE r (LetTele e) = LetTele (applyE r e)

instance Shiftable Tele where
  shift = shiftFromApplyE @Exp
instance Subst Exp Tele where
  applyE r (Body e) = Body (applyE r e)
  applyE r (LetStar e1 e2) = LetStar (applyE r e1) (applyE r e2)

----------------------------------------------
-- Display (Show)
----------------------------------------------

-- | To show lambda terms, we use a simple recursive instance of
-- Haskell's `Show` type class. In the case of a binder, we use the `getBody`
-- operation to access the body of the lambda expression.
instance Show (Exp n) where
  showsPrec :: Int -> Exp n -> String -> String
  showsPrec _ (Var x) = shows x
  showsPrec d (App e1 e2) =
    showParen True $
      showsPrec 10 e1
        . showString " "
        . showsPrec 11 e2
  showsPrec d (Lam b) =
    showParen True $
      showString "λ. "
        . shows (getBody b)
  showsPrec d (Let e1 e2) =
    showParen True $
      showString "let "
        . showsPrec 10 e1
        . showString " in "
        . shows (getBody e2)
  showsPrec d (LetRec e1 e2) =
    showParen True $
      showString "let rec "
        . shows (getBody e1)
        . showString " in "
        . shows (getBody e2)
  showsPrec d (LetTele e) = showString "<let-tele>"

-----------------------------------------------
-- (big-step) evaluation
-----------------------------------------------

-- >>> eval t1
-- (λ. (λ. (1 ((λ. 0) 0))))

-- >>> eval (t1 `App` t0)
-- (λ. ((λ. 0) ((λ. 0) 0)))

-- >>> eval t2
-- (λ. 0)

-- This one is an infinite loop
-- >>> eval t3
-- ProgressCancelledException

-- >>> eval t4
-- (λ. 0)

eval :: Exp n -> Exp n
eval (Var x) = Var x
eval (Lam b) = Lam b
eval (App e1 e2) =
  let v = eval e2
   in case eval e1 of
        Lam b -> eval (instantiate b v)
        t -> App t v
eval (Let e1 e2) =
  eval (instantiate e2 (eval e1))
eval (LetRec e1 e2) =
  -- use a Haskell recursive definition
  -- to tie the knot for a recursive definition
  -- in the object language
  let v = instantiate e1 v
   in eval (instantiate e2 v)
eval (LetTele e) = evalTele e

evalTele :: Tele n -> Exp n
evalTele (Body e) = eval e
evalTele (LetStar e t) =
  evalTele (instantiate t (eval e))

--------------------------------------------------------
-- environment based evaluation / normalization
--------------------------------------------------------

evalEnv :: Env Exp m n -> Exp m -> Exp n
evalEnv r (Var x) = applyEnv r x
evalEnv r (Lam b) = applyE r (Lam b)
evalEnv r (App e1 e2) =
  let v = evalEnv r e2
   in case evalEnv r e1 of
        Lam b ->
          unbindWith b (\r' e' -> evalEnv (v .: r') e')
        t -> App t v
evalEnv r (Let e1 e2) =
  let v = evalEnv r e1
   in unbindWith e2 (\r' e' -> evalEnv (v .: (r' .>> r)) e')
evalEnv r (LetRec e1 e2) =
  let v = unbindWith e1 (\r' e' -> evalEnv (v .: (r' .>> r)) e')
   in unbindWith e2 (\r' e' -> evalEnv (v .: (r' .>> r)) e')
evalEnv r (LetTele e) = evalTeleEnv r e

evalTeleEnv :: Env Exp m n -> Tele m -> Exp n
evalTeleEnv r (Body e) = evalEnv r e
evalTeleEnv r (LetStar e1 e2) =
  let v = evalEnv r e1
   in unbindWith e2 (\r' e' -> evalTeleEnv (v .: (r' .>> r)) e')

-- >>> evalEnv zeroE t1     -- start with "empty environment"
-- λ. λ. 1 (λ. 0 0)

-- >>> evalEnv zeroE t2
-- (λ. 0)

-- >>> evalEnv zeroE t4
-- (λ. 0)

----------------------------------------------------------------
