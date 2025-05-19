-- | A dependent type system, with nested dependent pattern matching for Sigma types.
-- This is an advanced usage of the binding library, demonstrating the use of Scoped patterns.
-- It doesn't correspond to any current system, but has its own elegance
-- (Maybe deserves to be written up on its own?)
-- However, this implementation does not attempt to use explicit environments
-- to optimize the execution.
module DepMatch where

import AutoEnv
import AutoEnv.Context


import qualified AutoEnv.Bind.Pat as Pat
import qualified AutoEnv.Bind.Scoped as Scoped
import AutoEnv.Bind.PatN as PN

import Control.Monad (guard, zipWithM_)
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Data.Fin
import Data.List qualified as List
import Data.Maybe qualified as Maybe
import Data.Vec qualified
import Debug.Trace
import Text.ParserCombinators.Parsec.Pos (SourcePos, newPos)

-- In this system, `Match` introduces a Pi type and generalizes
-- dependent functions
-- If the pattern is a single variable, or an annotated variable,
-- then the `Match` term is just a normal lambda expression.
-- But the pattern could be more structured than that, supporting
-- a general form of pattern matching. In this simple language,
-- only type that supports pattern matching is a Sigma type. So
-- every match expression should have a single branch. But, for
-- generality, we pretend that more are possible.
data Exp (n :: Nat)
  = Star
  | Pi (Exp n) (Bind1 Exp Exp n)
  | Var (Fin n)
  | Match [Branch n]  -- case lambda
  | App (Exp n) (Exp n)
  | Sigma (Exp n) (Bind1 Exp Exp n)
  | Pair (Exp n) (Exp n)
  | Annot (Exp n) (Exp n)

-- | A single branch in a match expression. Binds a pattern
-- with expression variables, within some expression body
data Branch (n :: Nat)
  = forall p. Branch (Scoped.Bind Exp Exp (Pat p) n)


-- | Patterns, which may include embedded type annotations
-- `p` is the number of variables bound by the pattern
-- `n` is the number of free variables in type annotations in the pattern
data Pat (p :: Nat) (n :: Nat) where
  PVar :: Pat N1 n
  -- Patterns are "telescopic"
  -- In Pair pattern, we increase the scope so that variables
  -- bound in the left subterm can be referred to in the right subterm
  PPair :: Pat p1 n -> Pat p2 (p1 + n) -> Pat (p2 + p1) n
  -- Patterns can also include type annotations.
  PAnnot :: Pat p n -> Exp n -> Pat p n


-- This definitions support telescopes: variables bound earlier in the pattern
-- can appear later.  For example, the pattern for a type paired with
-- a term of that type can look like this
--     (x, (y :: x))

pat0 :: Pat N2 N0
pat0 = PPair PVar (PAnnot PVar (Var f0))

-- The type of this pattern is
--     Sigma x:Star.x
ty0 :: Exp Z
ty0 = Sigma Star (bind1 (Var f0))

-------------------------------------------------------
-- definitions for pattern matching
-------------------------------------------------------

-- For any pattern type, we need to be able to calculate
-- the number of binding variables, both statically and dynamically
instance Sized (Pat p n) where
  type Size (Pat p n) = p
  size :: Pat p n -> SNat p
  size PVar = s1
  size (PPair p1 p2) = sPlus (size p2) (size p1)
  size (PAnnot p _) = size p

instance Scoped.ScopedSized (Pat p) where
  type ScopedSize (Pat p) = p

instance Scoped.IScopedSized Pat

-- A term that matches the "(x,(y:x))" and has type exists x:*. x
tm0 :: Exp Z
tm0 = Pair Star ty0

-- >>> patternMatch pat0 tm0
-- Just [(0,Sigma *. 0),(1,*)]

-- | Compare a pattern with an expression, potentially
-- producing a substitution for all of the variables
-- bound in the pattern
patternMatch :: forall p n. (SNatI n) => Pat p n -> Exp n -> Maybe (Env Exp p n)
patternMatch PVar e = Just $ oneE e
patternMatch (PPair p1 p2) (Pair e1 e2) =
  -- two append operations require implicit sizes in the context
  withSNat (Scoped.scopedSize p1) $ withSNat (Scoped.scopedSize p2) $ do
    env1 <- patternMatch p1 e1
    -- NOTE: substitute in p2 with env1 before pattern matching
    env2 <- patternMatch (applyE (env1 .++ idE) p2) e2
    return (env2 .++ env1)
-- ignore type annotates when pattern matching
patternMatch (PAnnot p _) e = patternMatch p e
patternMatch p (Annot e _) = patternMatch p e
patternMatch _ _ = Nothing

findBranch :: forall n. (SNatI n) => Exp n -> [Branch n] -> Maybe (Exp n)
findBranch e [] = Nothing
findBranch e (Branch (bnd :: Scoped.Bind Exp Exp (Pat p) n) : brs) =
  case patternMatch (Scoped.getPat bnd) e of
    Just r -> Just $ Scoped.instantiate bnd r
    Nothing -> findBranch e brs

----------------------------------------------

-- * Subst instances

instance SubstVar Exp where
  var = Var

instance Shiftable Exp where
  shift = shiftFromApplyE @Exp
instance Subst Exp Exp where
  applyE r Star = Star
  applyE r (Pi a b) = Pi (applyE r a) (applyE r b)
  applyE r (Var x) = applyEnv r x
  applyE r (App e1 e2) = App (applyE r e1) (applyE r e2)
  applyE r (Sigma a b) = Sigma (applyE r a) (applyE r b)
  applyE r (Pair a b) = Pair (applyE r a) (applyE r b)
  applyE r (Match brs) = Match (map (applyE r) brs)
  applyE r (Annot a t) = Annot (applyE r a) (applyE r t)

instance Shiftable (Pat p) where
  shift = shiftFromApplyE @Exp
instance Subst Exp (Pat p) where
  applyE :: Env Exp n m -> Pat p n -> Pat p m
  applyE r PVar = PVar
  -- need to account for new pattern variables from p1 bound in p2
  applyE r (PPair p1 p2) = PPair (applyE r p1) (applyE (upN (size p1) r) p2)
  applyE r (PAnnot p t) = PAnnot (applyE r p) (applyE r t)

instance Shiftable Branch where
  shift = shiftFromApplyE @Exp
instance Subst Exp Branch where
  applyE :: forall n m. Env Exp n m -> Branch n -> Branch m
  applyE r (Branch b) = Branch (applyE r b)

----------------------------------------------
-- Free variable calculation
----------------------------------------------

t00 :: Exp N2
t00 = App (Var f0) (Var f0)

t01 :: Exp N2
t01 = App (Var f0) (Var f1)

-- >>> appearsFree f0 t00
-- True

-- >>> appearsFree f1 t00
-- False

instance FV Exp where
  appearsFree n (Var x) = n == x
  appearsFree n Star = False
  appearsFree n (Pi a b) = appearsFree n a || appearsFree (FS n) (getBody1 b)
  appearsFree n (App a b) = appearsFree n a || appearsFree n b
  appearsFree n (Sigma a b) = appearsFree n a || appearsFree (FS n) (getBody1 b)
  appearsFree n (Pair a b) = appearsFree n a || appearsFree n b
  appearsFree n (Match b) = any (appearsFree n) b
  appearsFree n (Annot a t) = appearsFree n a || appearsFree n t

instance FV Branch where
  appearsFree n (Branch bnd) = appearsFree n bnd

instance FV (Pat p) where
  appearsFree n PVar = False
  appearsFree n (PPair p1 p2) = appearsFree n p1 || appearsFree (shiftN (size p1) n) p2
  appearsFree n (PAnnot p t) = appearsFree n p || appearsFree n t

----------------------------------------------
-- weakening (convenience functions)
----------------------------------------------

-- >>> :t weaken' s1 t00
-- weaken' s1 t00 :: Exp ('S ('S N1))

-- >>> weaken' s1 t00
-- 0 0

weaken' :: SNat m -> Exp n -> Exp (m + n)
weaken' m = applyE @Exp (weakenE' m)

weakenBind' :: SNat m -> Bind1 Exp Exp n -> Bind1 Exp Exp (m + n)
weakenBind' m = applyE @Exp (weakenE' m)

----------------------------------------------
-- strengthening
----------------------------------------------

-- >>> strengthen' s1 s1 t00
-- Just (0 0)

-- >>> strengthen' s1 s1 t01
-- Nothing

instance Strengthen Exp where
  strengthenRec k m n (Var x) = Var <$> strengthenRec k m n x
  strengthenRec k m n Star = pure Star
  strengthenRec k m n (Pi a b) = Pi <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (App a b) = App <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (Pair a b) = Pair <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (Sigma a b) = Sigma <$> strengthenRec k m n a <*> strengthenRec k m n b
  strengthenRec k m n (Match b) = Match <$> mapM (strengthenRec k m n) b
  strengthenRec k m n (Annot a t) = Annot <$> strengthenRec k m n a <*> strengthenRec k m n t

instance Strengthen (Pat p) where
  strengthenRec k m n PVar = pure PVar
  strengthenRec (k :: SNat k) (m :: SNat m) (n :: SNat n) (PPair (p1 :: Pat p1 (k + (m + n)))
    (p2 :: Pat p2 (p1 + (k + (m + n))))) =
      case (axiomAssoc @p1 @k @(m + n),
            axiomAssoc @p1 @k @n) of
       (Refl, Refl) ->
         let r = strengthenRec (sPlus (Scoped.iscopedSize p1) k) m n p2 in
         PPair <$> strengthenRec k m n p1
                             <*> r
  strengthenRec k m n (PAnnot p1 e2) = PAnnot <$> strengthenRec k m n p1 <*> strengthenRec k m n e2

instance Strengthen Branch where

  strengthenRec k m n (Branch bnd) = Branch <$> strengthenRec k m n bnd
----------------------------------------------
-- Some Examples
----------------------------------------------

star :: Exp n
star = Star

-- No annotation on the binder
lam :: Exp (S n) -> Exp n
lam b = Match [Branch (Scoped.bind PVar b)]

-- Annotation on the binder
alam :: Exp n -> Exp (S n) -> Exp n
alam t b = Match [Branch (Scoped.bind (PAnnot PVar t) b)]

-- The identity function "λ x. x". With de Bruijn indices
-- we write it as "λ. 0", though with `Match` it looks a bit different
t0 :: Exp Z
t0 = lam (Var f0)

-- A larger term "λ x. λy. x (λ z. z z)"
-- λ. λ. 1 (λ. 0 0)
t1 :: Exp Z
t1 =
  lam
    ( lam
        (Var f1 `App` lam (Var f0 `App` Var f0))
    )

-- To show lambda terms, we can write a simple recursive instance of
-- Haskell's `Show` type class. In the case of a binder, we use the `unbind`
-- operation to access the body of the lambda expression.

-- >>> t0
-- λ_. 0

-- >>> t1
-- λ_. (λ_. (1 (λ_. (0 0))))

-- Polymorphic identity function and its type

tyid = Pi star (bind1 (Pi (Var f0) (bind1 (Var f1))))

tmid = lam (lam (Var f0))

-- >>> tyid
-- Pi *. 0 -> 1

-- >>> tmid
-- λ_. (λ_. 0)

--------------------------------------------------------

-- * Show instances

--------------------------------------------------------


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
  showsPrec d (Pair e1 e2) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString ", "
        . showsPrec 11 e2
  showsPrec d (Match [b]) =
    showParen (d > 10) $
      showString "λ"
        . showsPrec 10 b
  showsPrec d (Match b) =
    showParen (d > 10) $
      showString "match"
        . showsPrec 10 b
  showsPrec d (Annot a t) =
    showParen (d > 10) $
      showsPrec 10 a
        . showString " : "
        . showsPrec 10 t

instance Show (Branch b) where
  showsPrec d (Branch b) =
    showsPrec 10 (Scoped.getPat b)
      . showString ". "
      . showsPrec 11 (Scoped.getBody b)

instance Show (Pat p n) where
  showsPrec d PVar = showString "_"
  showsPrec d (PPair e1 e2) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString ", "
        . showsPrec 11 e2
  showsPrec d (PAnnot e1 e2) =
    showParen (d > 0) $
      showsPrec 10 e1
        . showString " : "
        . showsPrec 11 e2

--------------------------------------------------------

-- * Alpha equivalence

--------------------------------------------------------

-- NOTE: this is not the same type as patEq
instance PatEq (Pat p1 n) (Pat p2 n) where
  patEq :: Pat p1 n -> Pat p2 n -> Maybe (p1 :~: p2)
  patEq PVar PVar = Just Refl
  patEq (PPair p1 p2) (PPair p1' p2') = do
    Refl <- patEq p1 p1'
    Refl <- patEq p2 p2'
    return Refl
  patEq (PAnnot p1 p2) (PAnnot p1' p2') = do
    Refl <- patEq p1 p1'
    guard (p2 == p2')
    return Refl
  patEq _ _ = Nothing

instance Eq (Branch n) where
  (==) :: Branch n -> Branch n -> Bool
  (Branch (p1 :: Scoped.Bind Exp Exp (Pat m1) n))
    == (Branch (p2 :: Scoped.Bind Exp Exp (Pat m2) n)) =
      case testEquality
        (Scoped.scopedSize (Scoped.getPat p1) :: SNat m1)
        (Scoped.scopedSize (Scoped.getPat p2) :: SNat m2) of
        Just Refl -> p1 == p2
        Nothing -> False

-- To compare pattern binders, we need to unbind, but also
-- make sure that the patterns are equal
instance (Eq (Exp n)) => Eq (Scoped.Bind Exp Exp (Pat m) n) where
  b1 == b2 =
    Maybe.isJust (patEq (Scoped.getPat b1) (Scoped.getPat b2))
      && Scoped.getBody b1 == Scoped.getBody b2

-- To compare binders, we only need to `unbind` them
instance (Eq (Exp n)) => Eq (Bind1 Exp Exp n) where
  b1 == b2 = getBody1 b1 == getBody1 b2

instance (Eq (Exp n)) => Eq (PN.Bind2 Exp Exp n) where
  b1 == b2 = getBody2 b1 == getBody2 b2

-- With the instance above the derivable equality instance
-- is alpha-equivalence
deriving instance (Eq (Exp n))

--------------------------------------------------------

-- * big-step evaluation

--------------------------------------------------------

-- We can write the usual operations for evaluating
-- lambda terms to values

-- >>> eval t1
-- λ_. (λ_. (1 (λ_. (0 0))))

-- >>> eval (t1 `App` t0)
-- λ_. (λ_. 0 (λ_. (0 0)))

-- OLD
-- λ. λ. 0 (λ. 0 0)

eval :: (SNatI n) => Exp n -> Exp n
eval (Var x) = Var x
eval (Match b) = Match b
eval (App e1 e2) =
  let v = eval e2
   in case eval e1 of
        Match b -> case findBranch v b of
          Just e -> eval e
          Nothing -> error "pattern match failure"
        t -> App t v
eval Star = Star
eval (Pi a b) = Pi a b
eval (Sigma a b) = Sigma a b
eval (Annot a t) = eval a
eval (Pair a b) = Pair a b

-- small-step evaluation

-- >>> step (t1 `App` t0)
-- Just (λ_. (λ_. 0 (λ_. (0 0))))

step :: (SNatI n) => Exp n -> Maybe (Exp n)
step (Var x) = Nothing
step (Match b) = Nothing
step (App (Match bs) e2)
  | Just r <- findBranch e2 bs =
      Just r
step (App e1 e2)
  | Just e1' <- step e1 = Just (App e1' e2)
  | Just e2' <- step e2 = Just (App e1 e2')
  | otherwise = Nothing
step Star = Nothing
step (Pi a b) = Nothing
step (Sigma a b) = Nothing
step (Pair a b) = Nothing
step (Annot a t) = step a

eval' :: (SNatI n) => Exp n -> Exp n
eval' e
  | Just e' <- step e = eval' e'
  | otherwise = e

----------------------------------------------------------------
-- Check for equality
----------------------------------------------------------------
data Err where
  NotEqual :: Exp n -> Exp n -> Err
  PiExpected :: Exp n -> Err
  PiExpectedPat :: Pat p1 n1 -> Err
  SigmaExpected :: Exp n -> Err
  VarEscapes :: Exp n -> Err
  PatternMismatch :: Pat p1 n1 -> Pat p2 n2 -> Err
  PatternTypeMismatch :: Pat p1 n1 -> Exp n1 -> Err
  AnnotationNeeded :: Exp n -> Err
  AnnotationNeededPat :: Pat p1 n1 -> Err

deriving instance (Show Err)

-- find the head form
whnf :: (SNatI n) => Exp n -> Exp n
whnf (App a1 a2) = case whnf a1 of
  Match bs -> case findBranch (eval a2) bs of
    Just b -> whnf b
    Nothing -> App (Match bs) a2
  t -> App t a2
whnf (Annot a t) = whnf a
whnf a = a

equate :: (MonadError Err m, SNatI n) => Exp n -> Exp n -> m ()
equate t1 t2 = do
  let n1 = whnf t1
      n2 = whnf t2
  equateWHNF n1 n2

equatePat ::
  forall p1 p2 m n.
  (MonadError Err m, SNatI n) =>
  Pat p1 n ->
  Pat p2 n ->
  m ()
equatePat PVar PVar = pure ()
equatePat (PPair p1 p1') (PPair p2 p2')
  | Just Refl <- testEquality (Scoped.scopedSize p1) (Scoped.scopedSize p2) =
      withSNat (sPlus (Scoped.scopedSize p1) (snat @n)) $
        equatePat p1 p2 >> equatePat p1' p2'
equatePat (PAnnot p1 e1) (PAnnot p2 e2) =
  equatePat p1 p2 >> equate e1 e2
equatePat p1 p2 = throwError (PatternMismatch p1 p2)

equateBranch :: (MonadError Err m, SNatI n) => Branch n -> Branch n -> m ()
equateBranch (Branch b1) (Branch b2) =
  Scoped.unbind b1 $ \(p1 :: Pat p1 n) body1 ->
    Scoped.unbind b2 $ \(p2 :: Pat p2 n) body2 ->
      case testEquality (Scoped.scopedSize p1) (Scoped.scopedSize p2) of
        Just Refl ->
          equatePat p1 p2 >> equate body1 body2
        Nothing ->
          throwError (PatternMismatch (Scoped.getPat b1) (Scoped.getPat b2))

equateWHNF :: (SNatI n, MonadError Err m) => Exp n -> Exp n -> m ()
equateWHNF n1 n2 =
  case (n1, n2) of
    (Star, Star) -> pure ()
    (Var x, Var y) | x == y -> pure ()
    (Match b1, Match b2) ->
      zipWithM_ equateBranch b1 b2
    (App a1 a2, App b1 b2) -> do
      equateWHNF a1 b1
      equate a2 b2
    (Pi tyA1 b1, Pi tyA2 b2) -> do
      equate tyA1 tyA2
      equate (getBody1 b1) (getBody1 b2)
    (Sigma tyA1 b1, Sigma tyA2 b2) -> do
      equate tyA1 tyA2
      equate (getBody1 b1) (getBody1 b2)
    (_, _) -> throwError (NotEqual n1 n2)

----------------------------------------------------------------

-- * Type checking

----------------------------------------------------------------


inferPattern ::
  (MonadError Err m, SNatI n) =>
  Ctx Exp n -> -- input context
  Pat p n -> -- pattern to check
  m (Ctx Exp (p + n), Exp (p + n), Exp n)
inferPattern g (PAnnot p ty) = do
  (g', e) <- checkPattern g p ty
  pure (g', e, ty)
inferPattern g p = throwError (AnnotationNeededPat p)

-- | type check a pattern and produce an extended typing context,
-- plus expression form of the pattern (for dependent pattern matching)

-- TODO: do we need to pass in the context? Can we just make it an
-- output of the function?
checkPattern ::
  forall m n p.
  (MonadError Err m, SNatI n) =>
  Ctx Exp n -> -- input context
  Pat p n -> -- pattern to check
  Exp n -> -- expected type of pattern (should be in whnf)
  m (Ctx Exp (p + n), Exp (p + n))
checkPattern g PVar a = do
  pure (g +++ a, var f0)
checkPattern g (PPair (p1 :: Pat p1 n) (p2 :: Pat p2 (p1 + n))) (Sigma tyA tyB) =
  -- The context for the recursive call on p2 needs a little preparation
  -- need to have implicit version of p1 + n
  withSNat (sPlus (Scoped.scopedSize p1) (snat @n)) $
  -- need to know that Plus is associative
  case axiomAssoc @p2 @p1 @n of
  Refl -> do
    (g', e1) <- checkPattern g p1 tyA
    let tyB' = weakenBind' (Scoped.scopedSize p1) tyB
    let tyB'' = whnf (instantiate1 tyB' e1)
    (g'', e2) <- checkPattern g' p2 tyB''
    let e1' = weaken' (Scoped.scopedSize p2) e1
    return (g'', Pair e1' e2)
checkPattern g p ty = do
  (g', e, ty') <- inferPattern g p
  equate ty ty'
  return (g', e)

-----------------------------------------------------------
-- Checking branches
-----------------------------------------------------------

--      G |- p : A => G'      G' |- b : B { p / x}
--   ----------------------------------------------
--       G |- p => b : Pi x : A . B

checkBranch ::
  forall m n.
  (MonadError Err m, SNatI n) =>
  Ctx Exp n ->
  Exp n ->
  Branch n ->
  m ()
checkBranch g (Pi tyA tyB) (Branch bnd) =
  Scoped.unbind bnd $ \(pat :: Pat p n) body -> do
    let p = Scoped.scopedSize pat

    -- find the extended context and pattern expression
    (g', a) <- checkPattern g pat tyA

    -- shift tyB to the scope of the pattern and instantiate it with 'a'
    -- must be done simultaneously because 'a' is from a larger scope
    let tyB' = applyE (a .: shiftNE p) (getBody1 tyB)

    -- check the body of the branch in the scope of the pattern
    checkType g' body tyB'
checkBranch g t e = throwError (PiExpected t)

-- should only check with a type in whnf
checkType ::
  forall n m.
  (MonadError Err m, SNatI n) =>
  Ctx Exp n ->
  Exp n ->
  Exp n ->
  m ()
checkType g (Pair a b) ty = do
  tyA <- inferType g a
  tyB <- inferType g b
  case ty of
    (Sigma tyA tyB) -> do
      checkType g a tyA
      checkType g b (instantiate1 tyB a)
    _ -> throwError (SigmaExpected ty)
checkType g (Match bs) ty = do
  mapM_ (checkBranch g ty) bs
checkType g e t1 = do
  t2 <- inferType g e
  equate (whnf t2) t1

-- | infer the type of an expression. This type may not
-- necessarily be in whnf
inferType ::
  forall n m.
  (MonadError Err m, SNatI n) =>
  Ctx Exp n ->
  Exp n ->
  m (Exp n)
inferType g (Var x) = pure (applyEnv g x)
inferType g Star = pure star
inferType g (Pi a b) = do
  checkType g a star
  checkType (g +++ a) (getBody1 b) star
  pure star
inferType g (App a b) = do
  tyA <- inferType g a
  case whnf tyA of
    Pi tyA1 tyB1 -> do
      checkType g b tyA1
      pure $ instantiate1 tyB1 b
    t -> throwError (PiExpected t)
inferType g (Sigma a b) = do
  checkType g a star
  checkType (g +++ a) (getBody1 b) star
  pure star
inferType g a =
  throwError (AnnotationNeeded a)

-- >>> tmid
-- λ_. (λ_. 0)

-- >>> tyid
-- Pi *. 0 -> 1

-- >>> :t tyid
-- tyid :: Exp n

-- >>> (checkType zeroE tmid tyid :: Either Err ())
-- Right ()

-- >>> (inferType zeroE (App tmid tyid) :: Either Err (Exp N0))
-- Left (AnnotationNeeded (λ_. (λ_. 0)))
