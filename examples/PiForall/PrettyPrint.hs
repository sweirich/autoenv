-- | A Pretty Printer.
module PiForall.PrettyPrint (Display (..), D (..), SourcePos, PP.Doc, pp, disp, debug, DispInfo, initDI, namesDI) where

import Control.Monad.Reader (MonadReader (ask, local), asks)
import Data.Set qualified as S
import qualified Data.Map as Map

import Text.ParserCombinators.Parsec.Error (ParseError)
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceColumn, sourceLine, sourceName)
import Prettyprinter (Doc, (<+>))
import qualified Prettyprinter as PP

import AutoEnv.Lib
import AutoEnv.Classes
import AutoEnv.Context
import AutoEnv.Env
import AutoEnv.Bind.Local as Local
import AutoEnv.Bind.Scoped (TeleList(..))
import qualified AutoEnv.Bind.Scoped as Scoped
import AutoEnv.Bind.Pat (PatList(..))
import qualified AutoEnv.Bind.Pat as Pat


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
class Display d where
  display :: d -> DispInfo -> Doc e

-- | Convenience entry point for the pretty printer
pp :: Display d => d -> String
pp p = show (display p initDI)

disp :: Display d => d -> Doc e
disp x = display x initDI

-- | For debugging
debug :: Display d => d -> String
debug p = show (display p debugDI) where
    debugDI = initDI{showLongNames = True, showAnnots=True}

-- | The data structure for information about the display
data DispInfo = forall n. DI
  { -- | should we show type annotations?
    showAnnots :: Bool,
    -- | names that have been used
    dispAvoid :: S.Set GlobalName,
    -- | names currently in the local scope
    localNames :: [LocalName],
    -- | current precedence level
    prec :: Int,
    -- | should we print internally-generated names, or user-friendly versions
    showLongNames :: Bool
  }


-- | Scoped error message quoting
data D n = DS String 
         | forall a. Display a => DC a  -- closed constant, not a string
         | forall a. Display (a n) => DD (a n)  -- single displayable value
         | forall a. Display (a n) => DL [a n]  -- list of displayable values

initDI :: DispInfo 
initDI = DI { showAnnots = False,
              dispAvoid = S.empty,
              localNames = [],
              prec = 0,
              showLongNames = False
            }

namesDI :: [LocalName] -> DispInfo
namesDI s = initDI { localNames = s }


-------------------------------------------------------------------------

-- * Display Instances for quoting, errors, source positions, names

-------------------------------------------------------------------------

instance Display (D n) where
  display (DS s) di = PP.pretty s
  display (DD a) di = PP.nest 2 $ display a di
  display (DC c) di = disp c
  display (DL a) di =
    PP.brackets (PP.sep (PP.punctuate PP.comma (map (`display` di) a)))

instance Display ParseError where
  display ps di = PP.pretty (show ps)

instance Display SourcePos where
  display p di =
    PP.pretty (sourceName p) PP.<> PP.colon PP.<> PP.pretty (sourceLine p)
      PP.<> PP.colon
      PP.<> PP.pretty (sourceColumn p)
      PP.<> PP.colon


------------------------------------------------------------------------

-- * Display Instances for Modules

-------------------------------------------------------------------------


instance Display Module where
  display m = do
    dn <- display (moduleName m)
    di <- mapM display (moduleImports m)
    de <- mapM display (moduleEntries m)
    pure $ PP.vcat $ [PP.pretty "module" <+> dn <+> PP.pretty "where"]
                    ++ di ++ de


instance Display ModuleImport where
  display (ModuleImport i) = pure $ PP.pretty "import" <+> disp i


instance Display [ModuleEntry] where
  display ds = do
    dd <- mapM display ds
    pure $ PP.vcat dd

instance Display ModuleEntry where
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

instance Display DataDef where
    display (DataDef params sort constructors) = do
        dp <- display params
        ds <- display sort
        dc <- mapM display constructors
        pure $ PP.nest 2 (PP.vcat
            (dp
                <+> PP.colon
                <+> ds
                <+> PP.pretty "where"
             : dc ))

instance Display (ConstructorDef n) where
  display (ConstructorDef c TNil) = do
    pure $ PP.pretty c
  display (ConstructorDef c tele) = do
    dc <- display c
    dt <- display tele
    pure $ dc <+> PP.pretty "of" <+> dt

instance Display (Telescope m n) where
   display TNil = mempty
   display (TCons (LocalDecl x tm) tele) = do
    dtm   <- display tm 
    dtele <- local (push x) (display tele) 
    return $ PP.parens (if x /= internalName then
                    PP.pretty (show x) <+> PP.colon <+> dtm
                else dtm) <+> dtele
   display (TCons (LocalDef x tm) tele) = do
    dx <- display (Var x)
    dtm <- display tm
    dtele <- display tele
    return $ PP.brackets (dx <+> PP.equals <+> dtm) <+> dtele

instance Display (Refinement Term n) where
  display (Refinement r) di = 
    PP.sep (PP.punctuate PP.comma (map d (Map.toList r))) where
      d (x,tm) = display (Var x) di <+> PP.pretty "=" <+> display tm di 

-- This is Context n
instance SNatI m => Display (Env Term m n) where
  display r di = 
    let t = tabulate r in
    PP.sep (PP.punctuate PP.comma (map d t)) where
      d (x,tm) = PP.pretty (show x) <+> PP.pretty "~>" <+> display tm di 


-------------------------------------------------------------------------

-- * Disp Instances for Prelude types

-------------------------------------------------------------------------


displayMaybe :: (t -> DispInfo -> Doc d) -> Maybe t -> DispInfo -> Doc d
displayMaybe display m di = case m of
  (Just a) -> PP.pretty "Just" <+> display a di
  Nothing -> PP.pretty "Nothing"

instance Display a => Display (Maybe a) where
  display = displayMaybe display


displayEither :: (Display a, Display b) =>
    (forall a. Display a => a -> DispInfo -> Doc d) -> Either a b -> DispInfo -> Doc d
displayEither disp e di = case e of
     (Left a) -> PP.pretty "Left" <+> disp a di
     (Right a) -> PP.pretty "Right" <+> disp a di

instance (Display a, Display b) => Display (Either a b) where
  display = displayEither display


-------------------------------------------------------------------------

-- * Display instances for Prelude types used in AST

-------------------------------------------------------------------------

instance Display String where
  display = return . PP.pretty

instance Display Int where
  display = return . PP.pretty . show

instance Display Integer where
  display = return . PP.pretty . show

instance Display Double where
  display = return . PP.pretty . show

instance Display Float where
  display = return . PP.pretty . show

instance Display Char where
  display = return . PP.pretty . show

instance Display Bool where
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

instance Display (Term n) where
  display TyType = return $ PP.pretty "Type"
  display (Global x) = return $ PP.pretty x   -- TODO
  display (Var n) = do
    ln <- asks localNames
    case nthOpt ln (toInt n) of
      Just x -> return (PP.pretty $ show $ x)
      Nothing -> return (PP.pretty $ "V" ++ show (toInt n))
  display a@(Lam b) = do
    n <- ask prec
    (binds, body) <- withPrec levelLam $ gatherBinders a
    return $ parens (levelLam < n) $ (PP.pretty "\\" PP.<> PP.sep binds PP.<> PP.pretty ".") <+> PP.nest 2 body
  display (App f x) = do
    n <- ask prec
    df <- withPrec levelApp (display f)
    dx <- withPrec (levelApp+1) (display x)
    return $ parens (levelApp < n) $ df <+> dx
  display (Pi a bnd) = do
    Local.unbind bnd $ \(n, b) -> do
      p <- ask prec
      lhs <-
            if f0 `appearsFree` b
              then do
                dn <- display n
                da <- withPrec 0 (display a)
                return $ PP.parens (dn <+> PP.colon <+> da)
              else do
                withPrec (levelArrow+1) (display a)
      db <- local (push n) $ withPrec levelPi (display b)
      return $ parens (levelArrow < p) $ lhs <+> PP.pretty "->" <+> db
  display (Ann a b) = do
    sa <- ask showAnnots
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
      if f0 `appearsFree` tyB then do
        dx <- display x
        dA <- withPrec 0 $ display tyA
        dB <- local (push x) $ withPrec 0 $ display tyB
        return $
          PP.pretty "{" <+> dx <+> PP.pretty ":" <+> dA
            <+> PP.pretty "|"
            <+> dB
            <+> PP.pretty "}"
        else do
          p <- ask prec
          dA <- withPrec levelSigma $ display tyA
          dB <- withPrec levelSigma $ display tyB
          return $ parens (levelSigma < p) (dA PP.<+> PP.pretty "*" PP.<+> dB)
  display (DataCon "," [a, b]) = do
    p <- ask prec
    da <- withPrec levelProd $ display a
    db <- withPrec levelProd $ display b
    return $ parens (levelProd < p) (da PP.<> PP.pretty "," PP.<> db)
  display (Let a bnd) = do
    Local.unbind bnd $ \(x, b) -> do
      p <- ask prec
      da <- display a
      dx <- display x
      db <- local (push x) $ display b
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
    p <- ask prec
    dn <- display n
    dargs <- withPrec (levelApp+1) $ mapM display args
    return $
      parens (levelApp < p && not (null args)) (PP.hsep (dn:dargs))
  display (DataCon n args) = do
    p <- ask prec
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
    p <- ask prec
    da <- withPrec (levelApp+1) $ display a
    db <- withPrec (levelApp+1) $ display b
    return $ PP.parens $ (da <+> PP.pretty "=" <+> db)
  display TmRefl = do
    return $ PP.pretty "Refl"
  display (Contra ty) = do
    p <- ask prec
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


instance Display (Match n) where
  display (Branch bd) = do
    let pat = Pat.getPat bd
    dpat <- display pat
    dubd <- local (pushList (binders pat)) $ display (Pat.getBody bd)
    return $ dpat <+> PP.pretty "->" <+> PP.align dubd



binders :: Pattern p1 -> [LocalName]
binders (PatVar x) = [x]
binders (PatCon c args) = bindersList args

bindersList :: PatList Pattern p1 -> [LocalName]
bindersList PNil = []
bindersList (PCons p ps) = binders p ++ bindersList ps

instance Display (Pattern p) where
  display (PatCon c PNil)   = display c
  display (PatCon c args) = do
    p <- ask prec
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

instance Display (PatList Pattern p) where
  display PNil = mempty
  display (PCons p ps) = do
    da <- display p
    ds <- display ps
    return $ da <+> ds

instance Display LocalName where
  display l _ = PP.pretty (show l)

-------------------------------------------------------------------------

-- * Helper functions for displaying terms

-------------------------------------------------------------------------

push :: LocalName -> DispInfo -> DispInfo 
push n r = r { localNames = n:localNames r} 
    
pushList :: [LocalName] -> DispInfo -> DispInfo
pushList ns r = foldl (flip push) r ns

gatherBinders :: Term n -> DispInfo -> ([Doc d], Doc d)
gatherBinders (Lam b) =
  Local.unbind b $ \(n, body) -> do
    dn <- display n
    (rest, body') <- local (push n) $ gatherBinders body
    return (dn : rest, body')
gatherBinders body = do
  db <- display body
  return ([], db)


