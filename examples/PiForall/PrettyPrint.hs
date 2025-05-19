-- | A Pretty Printer.
module PiForall.PrettyPrint (Display (..), DisplayM (..), D (..), SourcePos, PP.Doc, pp, disp, debug, DispInfo,
initDI, debugDI, ppM, debugM, scopedDisplay, scopedDebug) where

import Control.Monad.Reader (MonadReader (ask, local), asks)
import Data.Set qualified as S
import qualified Data.Map as Map

import Text.ParserCombinators.Parsec.Error (ParseError)
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceColumn, sourceLine, sourceName)
import Prettyprinter (Doc, (<+>))
import qualified Prettyprinter as PP

import qualified Data.Fin as Fin
import qualified Data.Vec as Vec
import AutoEnv.Lib
import AutoEnv.Classes
import AutoEnv.Context
import AutoEnv.Env
import AutoEnv.Bind.Local as Local
import AutoEnv.Bind.Scoped (TeleList(..))
import qualified AutoEnv.Bind.Scoped as Scoped
import AutoEnv.Bind.Pat (PatList(..))
import qualified AutoEnv.Bind.Pat as Pat
import AutoEnv.MonadNamed

import PiForall.Syntax

import Data.List as List

-------------------------------------------------------------------------

-- * Classes and Types for Pretty Printing

-------------------------------------------------------------------------

-- | The 'Display' class governs all types which can be turned into 'Doc's
-- The `disp` function is the main entry point for the pretty printer
-- While pretty printing, de Bruijn indices are converted into strings
-- (if possible, using the original names from the source program) using
-- information shored in the DispInfo
class Display n d where
  display :: d -> DisplayM n (Doc e)

type DisplayM = ScopedReaderT LocalName ((->) DispInfo)

-- | Convenience entry point for the pretty printer
pp :: Display Z d => d -> String
pp p = show (disp p initDI)

-- | Convenience entry point for debugging
debug :: Display Z d => d -> String
debug p = show (disp p debugDI)

disp :: Display Z d => d -> DispInfo -> Doc e
disp x = runScopedReaderT (display x) emptyScope

-- Monadic versions of the above, for the case when there
-- are already names in scope

debugM :: (MonadScoped LocalName m, Display n d) => d -> m n String
debugM p = show <$> dispMonadScoped p debugDI

ppM :: (MonadScoped LocalName m, Display n d) => d -> m n String
ppM p = show <$> dispMonadScoped p initDI

dispMonadScoped :: (MonadScoped LocalName m) => Display n d => d -> DispInfo -> m n (Doc e)
dispMonadScoped x di = do
  s <- scope
  let p = runScopedReaderT (display x) s
  return (p di)

scopedDisplay :: Display n d => d -> Scope LocalName n -> Doc e
scopedDisplay x s = runScopedReaderT (display x) s initDI

scopedDebug :: Display n d => d -> Scope LocalName n -> Doc e
scopedDebug x s = runScopedReaderT (display x) s debugDI

-- | The data structure for information about the display
data DispInfo = DI
  { -- | should we show type annotations?
    showAnnots :: Bool,
    -- | names that have been used (currently unused)
    dispAvoid :: S.Set GlobalName,
    -- | precedence level
    prec :: Int,
    -- | should we print internally-generated names, or user-friendly versions (currently unused)
    showLongNames :: Bool
  }



-- | Scoped error message quoting
data D n = DS String
         | forall a. Display n a => DC a  -- closed constant, not a string
         | forall a. Display n (a n) => DD (a n)  -- single displayable value
         | forall a. Display n (a n) => DL [a n]  -- list of displayable values

initDI :: DispInfo
initDI = DI { showAnnots = False,
              dispAvoid = S.empty,
              prec = 0,
              showLongNames = False
            }

debugDI :: DispInfo
debugDI = initDI{showLongNames = True, showAnnots=True}


-------------------------------------------------------------------------

-- * Display Instances for quoting, errors, source positions, names

-------------------------------------------------------------------------

instance Display n (D n) where
  display (DS s) = return $ PP.pretty s
  display (DD a) = PP.nest 2 <$> display a
  display (DC c) = display c
  display (DL a) = do
    ds <- mapM display a
    return $ PP.brackets (PP.sep (PP.punctuate PP.comma ds))

instance Display n ParseError where
  display ps = return $ PP.pretty (show ps)

instance Display n SourcePos where
  display p = return $
    PP.pretty (sourceName p) PP.<> PP.colon PP.<> PP.pretty (sourceLine p)
      PP.<> PP.colon
      PP.<> PP.pretty (sourceColumn p)
      PP.<> PP.colon


------------------------------------------------------------------------

-- * Display Instances for Modules

-------------------------------------------------------------------------


instance Display Z Module where
  display m = do
    dn <- display (moduleName m)
    di <- mapM display (moduleImports m)
    de <- mapM display (moduleEntries m)
    pure $ PP.vcat $ [PP.pretty "module" <+> dn <+> PP.pretty "where"]
                    ++ di ++ de


instance Display Z ModuleImport where
  display (ModuleImport i) = do
     di <- display i
     pure $ PP.pretty "import" <+> di


instance Display Z [ModuleEntry] where
  display ds = do
    dd <- mapM display ds
    pure $ PP.vcat dd

instance Display Z ModuleEntry where
  display (ModuleDef n term) = do
    dn <- display n
    dt <- display term
    pure $ dn <+> PP.pretty "=" <+> dt
  display (ModuleDecl n ty) = do
    dn <- display n
    dt <- display ty
    pure $ dn <+> PP.pretty ":" <+> dt
  display (ModuleData n dataDef) = do
    dn <- display n
    dd <- display dataDef
    pure $ PP.pretty "data" <+> dn <+> dd

instance Display Z DataDef where
    display (DataDef (params :: Telescope n Z) sort constructors) = do
        dp <- display params
        ds <- display sort
        dc <- case axiomPlusZ @n of
                Refl -> push params $ mapM display constructors
        pure $ PP.nest 2 (PP.vcat
            (dp
                <+> PP.colon
                <+> ds
                <+> PP.pretty "where"
             : dc ))

instance Display n (ConstructorDef n) where
  display (ConstructorDef c TNil) = do
    pure $ PP.pretty c
  display (ConstructorDef c tele) = do
    dc <- display c
    dt <- display tele
    pure $ dc <+> PP.pretty "of" <+> dt

instance Display n (Telescope m n) where
   display TNil = return mempty
   display (TCons (LocalDecl x tm) tele) = do
    dtm   <- display tm
    dtele <- push x (display tele)
    return $ PP.parens (if x /= internalName then
                    PP.pretty (show x) <+> PP.colon <+> dtm
                else dtm) <+> dtele
   display (TCons (LocalDef x tm) tele) = do
    dx <- display (Var x)
    dtm <- display tm
    dtele <- display tele
    return $ PP.brackets (dx <+> PP.equals <+> dtm)

instance Display n (Refinement Term n) where
  display (Refinement r) = do
    let d (x,tm) = do
                      dx <- display (Var x)
                      dt <- display tm
                      return $ dx <+> PP.pretty "=" <+> dt
    dr <- mapM d (Map.toList r)
    return $ PP.sep (PP.punctuate PP.comma dr)


-- This is Context n
instance SNatI m => Display n (Env Term m n) where
  display r = do
    let t = tabulate r
    let d (x,tm) = do
                    dt <- display tm
                    return $ PP.pretty (show x) <+> PP.pretty "~>" <+> dt
    dt <- mapM d t
    return $ PP.sep (PP.punctuate PP.comma dt)



-------------------------------------------------------------------------

-- * Disp Instances for Prelude types

-------------------------------------------------------------------------


displayMaybe :: (t -> DisplayM n (Doc d)) -> Maybe t -> DisplayM n (Doc d)
displayMaybe display m = case m of
  (Just a) -> display a >>= \da -> return $ PP.pretty "Just" <+> da
  Nothing -> return $ PP.pretty "Nothing"

instance Display n a => Display n (Maybe a) where
  display = displayMaybe display


displayEither :: (Display n a, Display n b) =>
    (forall a. Display n a => a -> DisplayM n (Doc d)) -> Either a b -> DisplayM n (Doc d)
displayEither disp e = case e of
     (Left a) -> disp a >>= \da -> return $ PP.pretty "Left" <+> da
     (Right a) -> disp a >>= \da -> return $ PP.pretty "Right" <+> da

instance (Display n a, Display n b) => Display n (Either a b) where
  display = displayEither display


-------------------------------------------------------------------------

-- * Display instances for Prelude types used in AST

-------------------------------------------------------------------------

instance Display n String where
  display x = return (PP.pretty x)

instance Display n Int where
  display = return . PP.pretty . show

instance Display n Integer where
  display = return . PP.pretty . show

instance Display n Double where
  display = return . PP.pretty . show

instance Display n Float where
  display = return . PP.pretty . show

instance Display n Char where
  display = return . PP.pretty . show

instance Display n Bool where
  display = return . PP.pretty . show

-------------------------------------------------------------------------

-- * Display instances for Terms

-------------------------------------------------------------------------


levelApp :: Int
levelApp     = 10
levelIf :: Int
levelIf      = 0
levelLet :: Int
levelLet     = 0
levelCase :: Int
levelCase    = 0
levelLam :: Int
levelLam     = 0
levelPi :: Int
levelPi      = 0
levelSigma :: Int
levelSigma   = 0
levelProd :: Int
levelProd    = 0
levelArrow :: Int
levelArrow   = 5

withPrec :: MonadReader DispInfo m => Int -> m a -> m a
withPrec p = local (\d -> d { prec = p })

parens :: Bool -> Doc d -> Doc d
parens b = if b then PP.parens else id

brackets :: Bool -> Doc d -> Doc d
brackets b = if b then PP.brackets else id

nthOpt :: [a] -> Int -> Maybe a
nthOpt (x:xs) 0 = Just x
nthOpt (x:xs) n = nthOpt xs (n - 1)
nthOpt [] _ = Nothing

instance Display n (Term n) where
  display TyType = return $ PP.pretty "Type"
  display (Global x) = return $ PP.pretty x   -- TODO
  display (Var n) = do
    s <- scope
    return (PP.pretty (show (scope_names s Vec.! n)))
  display a@(Lam b) = do
    n <- asks prec
    (binds, body) <- withPrec levelLam $ gatherBinders a
    return $ parens (levelLam < n) $ (PP.pretty "\\" PP.<> PP.sep binds PP.<> PP.pretty ".") <+> PP.nest 2 body
  display (App f x) = do
    n <- asks prec
    df <- withPrec levelApp (display f)
    dx <- withPrec (levelApp+1) (display x)
    return $ parens (levelApp < n) $ df <+> dx
  display (Pi a bnd) = do
    Local.unbind bnd $ \(n, b) -> do
      p <- asks prec
      lhs <-
            if Fin.f0 `appearsFree` b
              then do
                dn <- display n
                da <- withPrec 0 (display a)
                return $ PP.parens (dn <+> PP.colon <+> da)
              else do
                withPrec (levelArrow+1) (display a)
      db <- push n $ withPrec levelPi (display b)
      return $ parens (levelArrow < p) $ lhs <+> PP.pretty "->" <+> db
  display (Ann a b) = do
    sa <- asks showAnnots
    if sa then do
      da <- withPrec 0 (display a)
      db <- withPrec 0 (display b)
      return $ PP.parens (da <+> PP.pretty ":" <+> db)
      else display a

  display (Pos _ e) = display e

  display (TyCon "(=)" [a, b]) = do
    da <- withPrec 0 (display a)
    db <- withPrec 0 (display b)
    return $ PP.parens (da <+> PP.pretty "=" <+> db)

  display (TyCon "Sigma" [tyA, Lam bnd]) =
    Local.unbind bnd $ \(x, tyB) -> do
      if Fin.f0 `appearsFree` tyB then do
        dx <- display x
        dA <- withPrec 0 $ display tyA
        dB <- push x $ withPrec 0 $ display tyB
        return $
          PP.pretty "{" <+> dx <+> PP.pretty ":" <+> dA
            <+> PP.pretty "|"
            <+> dB
            <+> PP.pretty "}"
        else do
          p <- asks prec
          dA <- withPrec levelSigma $ display tyA
          dB <- push x $ withPrec levelSigma $ display tyB
          return $ parens (levelSigma < p) (dA PP.<+> PP.pretty "*" PP.<+> dB)
  display (DataCon "," [a, b]) = do
    p <- asks prec
    da <- withPrec levelProd $ display a
    db <- withPrec levelProd $ display b
    return $ parens (levelProd < p) (da PP.<> PP.pretty "," PP.<> db)
  display (Let a bnd) = do
    Local.unbind bnd $ \(x, b) -> do
      p <- asks prec
      da <- display a
      dx <- display x
      db <- push x $ display b
      return $
        parens (levelLet < p) $
        PP.sep
          [ PP.pretty "let" <+> dx
              <+> PP.pretty "="
              <+> da
              <+> PP.pretty "in",
            db
          ]

  display t
    | Just i <- isNumeral t = display i
  display (TyCon n args) = do
    p <- asks prec
    dn <- display n
    dargs <- withPrec (levelApp+1) $ mapM display args
    return $
      parens (levelApp < p && not (null args)) (PP.hsep (dn:dargs))
  display (DataCon n args) = do
    p <- asks prec
    dn <- display n
    dargs <- withPrec (levelApp+1) $ mapM display args
    return $
      parens (levelApp < p && not (null args)) (PP.hsep (dn:dargs))
  display (Case scrut alts) = do
    p <- asks prec
    dscrut <- withPrec (levelCase+1) $ display scrut
    dalts <- withPrec 0 $ mapM display alts
    return $
      parens (levelCase < p) $ prettyCase dscrut dalts
  display (Subst a b) = do
    p <- asks prec
    da <- withPrec 0 $ display a
    db <- withPrec 0 $ display b
    return $
      parens (levelPi < p) $
      PP.sep
        [ PP.pretty "subst" <+> da,
          PP.pretty "by" <+> db
        ]
  display (TyEq a b) = do
    p <- asks prec
    da <- withPrec (levelApp+1) $ display a
    db <- withPrec (levelApp+1) $ display b
    return $ PP.parens $ (da <+> PP.pretty "=" <+> db)
  display TmRefl = do
    return $ PP.pretty "Refl"
  display (Contra ty) = do
    p <- asks prec
    dty <- display ty
    return $ parens (levelPi < p) $ PP.pretty "contra" <+> dty
  display TrustMe = return $ PP.pretty "TRUSTME"
  display PrintMe = return $ PP.pretty "PRINTME"
open        = PP.flatAlt PP.emptyDoc (PP.pretty "{ ")
close       = PP.flatAlt PP.emptyDoc (PP.pretty  " }")
separator   = PP.flatAlt PP.emptyDoc (PP.pretty "; ")
prettyCase :: Doc ann -> [Doc ann] -> Doc ann
prettyCase scrut xs =
  let top =  PP.pretty "case" <+> scrut <+> PP.pretty "of" in
  if null xs then top <+> PP.pretty "{ }" else
    -- PP.nest 2 (top <> PP.line <> PP.encloseSep open close separator xs)
    PP.nest 2 (top <> PP.hardline <> PP.vsep xs)
--  PP.group (PP.pretty "case" <+> scrut <+> PP.pretty "of" <+>
--            PP.align (PP.encloseSep open close separator xs))


instance Display n (Match n) where
  display (Branch bd) = do
    let pat = Pat.getPat bd
    dpat <- display pat
    dubd <- push pat $ display (Pat.getBody bd)
    return $ dpat <+> PP.pretty "->" <+> PP.align dubd



binders :: Pattern p1 -> [LocalName]
binders (PatVar x) = [x]
binders (PatCon c args) = bindersList args

bindersList :: PatList Pattern p1 -> [LocalName]
bindersList PNil = []
bindersList (PCons p ps) = binders p ++ bindersList ps

instance Display n (Pattern p) where
  display (PatCon c PNil)   = display c
  display (PatCon c args) = do
    p <- asks prec
    dc <- display c
    dargs <- withPrec (levelApp+1) $ display args
    return $
       parens (levelApp < p && nonnil args)
         (PP.hsep [dc,dargs])
      where
        nonnil :: PatList Pattern p -> Bool
        nonnil PNil = False
        nonnil (PCons _ _) = True


  display (PatVar x) = display x

instance Display n (PatList Pattern p) where
  display PNil = return mempty
  display (PCons p ps) = do
    da <- display p
    ds <- display ps
    return $ da <+> ds

instance Display n LocalName where
  display l = return $ PP.pretty (show l)

-------------------------------------------------------------------------

-- * Helper functions for displaying terms

-------------------------------------------------------------------------

-- push :: LocalName -> DispInfo -> DispInfo
-- push n r = r { localNames = n:localNames r}

-- pushList :: [LocalName] -> DispInfo -> DispInfo
-- pushList ns r = foldl (flip push) r ns

gatherBinders :: Term n -> DisplayM n ([Doc d], Doc d)
gatherBinders (Lam b) =
  Local.unbind b $ \(n, body) -> do
    dn <- display n
    (rest, body') <- push n $ gatherBinders body
    return (dn : rest, body')
gatherBinders body = do
  db <- display body
  return ([], db)


