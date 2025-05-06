-- |
-- Module      : LC
-- Description : Untyped lambda calculus
-- Stability   : experimental
--
-- An implementation of the untyped lambda calculus including evaluation
-- and small-step reduction.
--
-- This module demonstrates the use of well-scoped lambda calculus terms.
-- The natural number index `n` is the scoping level -- a bound on the number
-- of free variables that can appear in the term. If `n` is 0, then the
-- term must be closed.
module LC where

import AutoEnv
import AutoEnv.Bind.Single
import Data.Fin
import Data.Vec qualified

-- | Datatype of well-scoped lambda-calculus expressions
--
-- The `Var` constructor of this datatype takes an index that must
-- be strictly less than the bound. Note that the type `Fin (S n)`
-- has `n` different elements.

-- The `Lam` constructor binds a variable, using the the type `Bind`
-- from the library. The type arguments state that the binder is
-- for a single expression variable, inside an expression term, that may
-- have at most `n` free variables.
data Exp (n :: Nat) where
  Var :: Fin n -> Exp n
  Lam :: Bind Exp Exp n -> Exp n
  App :: Exp n -> Exp n -> Exp n

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

----------------------------------------------
-- (Alpha-)Equivalence
----------------------------------------------

-- | To compare binders, we need to `getBody` them
-- The `getBody` operation has type
-- `Bind Exp Exp n -> Exp (S n)`
-- as the body of the binder has one more free variable
instance (Eq (Exp n)) => Eq (Bind Exp Exp n) where
  b1 == b2 = getBody b1 == getBody b2

deriving instance Eq (Exp n)

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
-- bounded by m. It is equivalent to a total function of type:
--
--       Fin n -> Exp m
--
-- The function `applyEnv` looks up a mapping in
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
  applyE r e = gapplyE r e
deriving instance (Generic1 Exp)

-- >>> :info Rep1 Exp


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

-----------------------------------------------
-- (big-step) evaluation
-----------------------------------------------

-- >>> eval t1

-- >>> eval (t1 `App` t0)
-- (λ. ((λ. 0) ((λ. 0) 0)))


-- TODO: the above should pretty print as λ. (λ. 0) ((λ. 0) 0)

-- | Calculate the value of a lambda-calculus expression
-- This function looks like it uses call-by-value evaluation:
-- in an application it evaluates the argument `e2` before
-- using the `instantiate` function from the library to substitute
-- the bound variable of `Bind` by v. However, this is Haskell,
-- a lazy language, so that result won't be evaluated unless the
-- function actually uses its argument.
eval :: Exp Z -> Exp Z
eval (Var x) = case x of {}
eval (Lam b) = Lam b
eval (App e1 e2) =
  let v = eval e2
   in case eval e1 of
        Lam b -> eval (instantiate b v)
        t -> App t v

----------------------------------------------
-- small-step evaluation
----------------------------------------------
-- >>> step (t1 `App` t0)
-- Just (λ. ((λ. 0) ((λ. 0) 0)))

-- | Do one step of evaluation, if possible
-- If the function is already a value or is stuck
-- this function returns `Nothing`
step :: Exp n -> Maybe (Exp n)
step (Var x) = Nothing
step (Lam b) = Nothing
step (App (Lam b) e2) = Just (instantiate b e2)
step (App e1 e2)
  | Just e1' <- step e1 = Just (App e1' e2)
  | Just e2' <- step e2 = Just (App e1 e2')
  | otherwise = Nothing

-- | Evaluate the term as much as possible
eval' :: Exp n -> Exp n
eval' e
  | Just e' <- step e = eval' e'
  | otherwise = e

--------------------------------------------------------
-- full normalization
--------------------------------------------------------

-- | Calculate the normal form of a lambda expression. This
-- is like evaluation except that it also reduces in the bodies
-- of `Lam` expressions. In this case, we must first `getBody`
-- the binder and then rebind when finished
nf :: Exp n -> Exp n
nf (Var x) = Var x
nf (Lam b) = Lam (bind (nf (getBody b)))
nf (App e1 e2) =
  case nf e1 of
    Lam b -> nf (instantiate b (nf e2))
    t -> App t (nf e2)

-- >>> nf t0
-- (λ. 0)

-- >>> nf t1
-- (λ. (λ. (1 0)))

-- >>> nf (t1 `App` t0)
-- (λ. 0)

--------------------------------------------------------
-- environment based evaluation / normalization
--------------------------------------------------------
-- The `eval` and `nf` functions above duplicate work in the
-- case of beta-reductions (i.e. applications). In a call
--     `nf (instantiate b (nf e2))` we will normalize
-- `nf e2` for every use of the bound variable in the binder
-- b. This normalization should be fast, because the term is
-- already in normal form, but it is still redundant work.

-- To fix this we can rewrite the functions to manipulate the
-- environment explicitly. These operations are equivalent
-- to the definitions above, but they provide access to the
-- suspended substitution during the traversal of the term.

-- Below, if n is 0, then this function acts like an
-- "environment-based" bigstep evaluator. The result of
-- evaluating a lambda expression is a closure --- the body
-- of the lambda paired with its environment. That is exactly
-- what the implementation of bind does.

-- In the case of beta-reduction, the `unBindWith` operation
-- applies its argument to the environment and subterm in the
-- closure. In other words, this function calls `evalEnv`
-- recursively with the saved environment and body of the lambda term.
-- Because `evalEnv` takes the body of the lambda term directly,
-- without substitution, it doesn't do any repeat work.

-- >>> :t getBody
-- getBody :: (Subst v v, Subst v c) => Bind v c n -> c ('S n)


evalEnv :: Env Exp m n -> Exp m -> Exp n
evalEnv r (Var x) = applyEnv r x
evalEnv r (Lam b) = applyE r (Lam b)
evalEnv r (App e1 e2) =
  let v = evalEnv r e2
   in case evalEnv r e1 of
        Lam b ->
          instantiateWith b v evalEnv
          -- unbindWith b (\r' e' -> evalEnv (v .: r') e')
        t -> App t v

-- >>> evalEnv zeroE t1     -- start with "empty environment"
-- λ. λ. 1 (λ. 0 0)

-- For full reduction, we need to normalize under the binder too.
-- In this case, the `applyUnder` function takes care of the
-- necessary environment manipulation. It applies its argument (`nfEnv`)
-- to the modifed

-- >>> :t applyUnder nfEnv
-- applyUnder nfEnv :: Env Exp n1 n2 -> Bind Exp Exp n1 -> Bind Exp Exp n2
--
-- In the beta-reduction case, we could use `unbindWith` as above
-- but the `instantiateWith` function already captures exactly
-- this pattern.
nfEnv :: Env Exp m n -> Exp m -> Exp n
nfEnv r (Var x) = applyEnv r x
--nfEnv r2 (Lam b) = Lam $ unbindWith b $ \r1 e -> bind (nfEnv (up (r1 .>> r2)) e)
nfEnv r (Lam b) = Lam $ applyUnder nfEnv r b
nfEnv r (App e1 e2) =
  let n = nfEnv r e1
   in case nfEnv r e1 of
        Lam b -> instantiateWith b n nfEnv
        t -> App t (nfEnv r e2)

----------------------------------------------------------------
