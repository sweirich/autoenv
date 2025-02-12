module PiForall.Equal where

import PiForall.Syntax
import PiForall.Environment (TcMonad, Context )
import qualified PiForall.Environment as Env
import PiForall.PrettyPrint

import AutoEnv.Env as Env
import AutoEnv
import AutoEnv.MonadScoped
import AutoEnv.Bind.Pat as Pat
import AutoEnv.Bind.Local as L
import AutoEnv.Bind.Scoped as Scoped

import Prettyprinter as PP

import Debug.Trace

import Control.Monad(unless, zipWithM, zipWithM_)
import Control.Monad.Except (catchError)

-- | compare two expressions for equality
-- first check if they are alpha equivalent then
-- if not, weak-head normalize and compare
-- throw an error if they cannot be matched up
equate :: forall n. Term n -> Term n -> TcMonad n ()
equate t1 t2 | t1 == t2 = return ()
equate t1 t2 = do
  n1 <- whnf t1
  n2 <- whnf t2
  case (n1, n2) of
    (TyType, TyType) -> return ()
    (Var x,  Var y) | x == y -> return ()
    (Lam bnd1, Lam bnd2) -> do
      push @LocalName (Pat.getPat bnd1)
         (equate (L.getBody bnd1) (L.getBody bnd2))
    (App a1 a2, App b1 b2) ->
      equate a1 b1 >> equate a2 b2
    (Pi tyA1 bnd1, Pi tyA2 bnd2) -> do
      equate tyA1 tyA2
      push @LocalName (L.getLocalName bnd1)
        (equate (L.getBody bnd1) (L.getBody bnd2))
    (Let rhs1 bnd1, Let rhs2 bnd2) -> do
      equate rhs1 rhs2
      push @LocalName (L.getLocalName bnd1)
        (equate (L.getBody bnd1) (L.getBody bnd2))
    (TyCon c1 ts1, TyCon c2 ts2) | c1 == c2 ->
      zipWithM_ equateArgs [ts1] [ts2]
    (DataCon d1 a1, DataCon d2 a2) | d1 == d2 -> do
      equateArgs a1 a2
    (Case s1 brs1, Case s2 brs2)
      | length brs1 == length brs2 -> do
      equate s1 s2
      -- require branches to be in the same order
      -- on both expressions
      s <- scope @LocalName
      withSNat (scope_size s) $ do
        let
          matchBr :: Match n -> Match n -> TcMonad n ()
          matchBr (Branch bnd1) (Branch bnd2) =
              Pat.unbind bnd1 $ \p1 a1 ->
              Pat.unbind bnd2 $ \p2 a2 -> do
                Refl <- patEq p1 p2 `Env.whenNothing`
                        [DS "Cannot match branches in", DD n1, DS "and", DD n2]
                push @LocalName p1 (equate a1 a2)
        zipWithM_ matchBr brs1 brs2
    (TyEq a1 b1, TyEq a2 b2) -> do
      equate a1 a2
      equate b1 b2
    (TmRefl, TmRefl) -> pure ()
    (Subst a1 b1, Subst a2 b2) -> do
      equate a1 a2
      equate b1 b2
    (Contra a1, Contra a2) -> equate a1 a2
    (TrustMe, TrustMe) -> pure ()
    (_,_) -> tyErr n1 n2
 where tyErr n1 n2 = do
          Env.err [DS "Expected", DD n2,
                   DS "but found", DD n1]

-- | Match up args
equateArgs :: [Term n] -> [Term n] -> TcMonad n ()
equateArgs (a1:t1s) (a2:t2s)  = do
  equate a1 a2
  equateArgs t1s t2s
equateArgs [] []  = return ()
equateArgs a1 a2  = do
          Env.err [DS "Expected", DC (length a2),
                   DS "but found", DC (length a1) ]



-------------------------------------------------------

ensurePi :: Typ n -> TcMonad n (Typ n, L.Bind Term Typ n)
ensurePi aty = do
  nf <- whnf aty
  case nf of
    (Pi tyA bnd) -> return (tyA, bnd)
    _ -> Env.err [DS "Expected a function type but found ", DD aty]

ensureEq :: Typ n -> TcMonad n (Term n, Term n)
ensureEq aty = do
  nf <- whnf aty
  case nf of
    (TyEq a b) -> return (a,b)
    _ -> Env.err [DS "Expected an equality type but found", DD nf]

-- | Ensure that the given type 'ty' is some tycon applied to
--  params (or could be normalized to be such)
-- Throws an error if this is not the case
ensureTCon :: Term n -> TcMonad n (TyConName, [Term n])
ensureTCon aty = do
  nf <- whnf aty
  case nf of
    TyCon n params -> return (n, params)
    _ -> Env.err [DS "Expected a data type but found", DD nf]

-------------------------------------------------------
-- | Convert a term to its weak-head normal form.
-- | TODO: add explicit environment (?)
-- But need to find out the types of every binder
whnf :: forall n. Term n -> TcMonad n (Term n)
whnf (Global y) = (do
  x <- Env.lookupGlobalDef y
  whnf x)
     `catchError` \_ -> return (Global y)

whnf (Var x)  = do
  -- maybeDef <- Env.lookupDef x
  -- case maybeDef of
  --  (Just d) -> whnf d
  --  _ ->
          return (Var x)

whnf (App t1 t2)  = do
  nf <- whnf t1
  case nf of
    (Lam  bnd) -> do
      whnf (L.instantiate bnd t2)
    _ -> do
      return (App nf t2)
-- ignore/remove type annotations and source positions when normalizing
whnf (Ann tm _)  = whnf tm
whnf (Pos _ tm)  = whnf tm
whnf (Let rhs bnd) = do
   whnf (L.instantiate bnd rhs)

whnf (Case scrut mtchs) = do
  nf <- whnf scrut
  case nf of
    (DataCon d args) -> f mtchs  where
      f (Branch bnd : alts)  = (do
          let pat = Pat.getPat bnd
          ss <- patternMatches nf pat
          whnf (Pat.instantiate bnd ss))
            `catchError` \ _ -> f alts
      f [] = Env.err $ [DS "Internal error: couldn't find a matching",
                    DS "branch for", DD nf, DS "in"] ++ map DD mtchs
    _ -> return (Case nf mtchs)
whnf (Subst a b) = do
  nf <- whnf b
  case nf of
    TmRefl -> whnf a
    _ -> pure (Subst a nf)
whnf PrintMe = pure (DataCon "()" [])
-- all other terms are already in WHNF
-- don't do anything special for them
whnf tm = do
  return tm


instance Named LocalName (SNat p) where
  patLocals = go where
    go :: forall p. SNat p -> Vec p LocalName
    go SZ = VNil
    go (SS q) = LocalName ("_" ++ show (toInt (SS q))) ::: go q

-- | 'Unify' the two terms, producing a list of definitions that
-- must hold for the terms to be equal
-- If the terms are already equal, succeed with an empty list
-- If there is an obvious mismatch, fail with an error
-- If either term is "ambiguous" (i.e. neutral), give up and
-- succeed with an empty list
unify :: forall n. Term n -> Term n -> TcMonad n (Refinement Term n)
unify t1 t2 = do
     s <- scope @LocalName
     withSNat (scope_size s) $ go SZ t1 t2
  where
    go :: forall n p. SNatI n => SNat p -> Term (Plus p n) -> Term (Plus p n) -> TcMonad (Plus p n) (Refinement Term n)
    go p tx ty = withSNat (sPlus p (snat :: SNat n)) $ do
      (txnf :: Term (Plus p n)) <- whnf tx
      (tynf :: Term (Plus p n)) <- whnf ty
      if txnf == tynf
        then return Env.emptyR
        else case (txnf, tynf) of
          (Var x, Var y) | x == y -> return Env.emptyR
          (Var y, yty)   |
            Just (Var y') <- strengthenN p (Var y),
            Just yty' <- strengthenN p yty
            -> if not (y' `appearsFree` yty')
                then return (Env.singletonR (y', yty'))
                else return Env.emptyR
          (yty, Var y)  |
            Just (Var y') <- strengthenN p (Var y),
            Just yty' <- strengthenN p yty
            -> if not (y' `appearsFree` yty')
                then return (Env.singletonR (y', yty'))
                else return Env.emptyR
          (DataCon n1 a1, DataCon n2 a2)
            | n1 == n2 -> goArgs p a1 a2
          (TyCon s1 tms1, TyCon s2 tms2)
            | s1 == s2 -> goArgs p tms1 tms2
          (Lam bnd1, Lam bnd2) -> do
            push @LocalName (L.getLocalName bnd1)
              (go @n (SS p) (L.getBody bnd1) (L.getBody bnd2))
          (Pi tyA1 bnd1, Pi tyA2 bnd2) -> do
            ds1 <- go p tyA1 tyA2
            ds2 <-
              push @LocalName (L.getLocalName bnd1)
                (go @n (SS p) (L.getBody bnd1) (L.getBody bnd2))
            joinR ds1 ds2 `Env.whenNothing` [DS "cannot join refinements"]
          (TyEq a1 b1, TyEq a2 b2) -> do
            ds1 <- go p a1 a2
            ds2 <- go p b1 b2
            joinR ds1 ds2 `Env.whenNothing` [DS "cannot join refinements"]
          _ ->
            if amb txnf || amb tynf
              then return Env.emptyR
              else Env.err [DS "Cannot equate", DD txnf, DS "and", DD tynf]
    goArgs p (t1 : a1s) (t2 : a2s) = do
      ds  <- go p t1 t2
      ds' <- goArgs p a1s a2s
      joinR ds ds' `Env.whenNothing` [DS "cannot join refinements"]
    goArgs p [] [] = return Env.emptyR
    goArgs _ _ _ = Env.err [DS "internal error (unify)"]




-- | Is a term "ambiguous" when it comes to unification?
-- In general, elimination forms are ambiguous because there are multiple
-- solutions.
amb :: Term n -> Bool
amb (App t1 t2) = True
amb (Case _ _) = True
amb (Subst _ _) = True
amb _ = False



-- | Determine whether the pattern matches the argument
-- If so return the appropriate substitution
-- otherwise throws an error
patternMatches :: forall p n. Term n -> Pattern p
               -> TcMonad n (Env Term p n)
patternMatches e (PatVar _) = return (oneE e)
patternMatches (DataCon n args) (PatCon l ps)
  | l == n = patternMatchList args ps
patternMatches nf pat =
  Env.err [DS "arg", DD nf, DS "doesn't match pattern", DC pat]

patternMatchList :: forall p n. [Term n] -> PatList Pattern p -> TcMonad n (Env Term p n)
patternMatchList [] PNil = return zeroE
patternMatchList (e1 : es) (PCons p1 ps) = do
    env1 <- patternMatches e1 p1
    env2 <- patternMatchList es ps
    withSNat (size ps) $
      return (env2 .++ env1)
patternMatchList _ _ = Env.err [DS "pattern match failure"]
