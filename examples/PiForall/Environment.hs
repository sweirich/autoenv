module PiForall.Environment where

import Data.Fin qualified as Fin
import Data.List
import Data.Foldable (toList)
import Data.Maybe ( listToMaybe )
import Control.Monad.Except
    ( MonadError(..), ExceptT, runExceptT )
import Control.Monad.Reader
    ( MonadReader(local), ask, asks, ReaderT(..) )
import Control.Monad.IO.Class
import Text.ParserCombinators.Parsec.Pos (SourcePos)
import Prettyprinter ( Doc, vcat, sep, (<+>), nest, pretty )

import AutoEnv.Context

import AutoEnv
import AutoEnv.Env
import qualified AutoEnv.Bind.Pat as Pat
import AutoEnv.MonadNamed
import qualified AutoEnv.Bind.Local as Local
import PiForall.Syntax
import PiForall.PrettyPrint


-------------------------------------------------------

-- * environment and type checking monad

-------------------------------------------------------


-- | The type checking Monad includes error (for error reporting) and IO
-- (for warning messages).
-- The Environment contains global declarations and definitions.
newtype TcMonad n a = TcMonad (ReaderT (TcEnv n) (ExceptT Err IO) a)
  deriving (Functor, Applicative, Monad, MonadReader (TcEnv n), MonadError Err, MonadIO)

-- | Entry point for the type checking monad, given an
-- initial environment, returns either an error message
-- or some result.
runTcMonad :: TcMonad Z a -> IO (Either Err a)
runTcMonad (TcMonad m) = runExceptT (runReaderT m emptyEnv)

-- | Environment manipulation and accessing functions
data TcEnv n = TcEnv
  {
    -- | Datatype definitions, top-level declarations and definitions
    globals :: [ModuleEntry],
    -- | Type declarations: it's not safe to
    -- put these in the context until a corresponding term
    -- has been checked.
    hints :: [(GlobalName, Typ Z)],
    -- | what part of the file we are in (for errors/warnings)
    sourceLocation :: [SourceLocation],
    -- | the current scope of local variables
    env_scope :: Scope LocalName n,
    -- | current refinement for variables in scope
    env_refinement :: Refinement Term n
  }

instance MonadScoped LocalName TcMonad where
  scope = asks env_scope

  pushVec :: SNatI p => Vec p LocalName -> TcMonad (p + n) a -> TcMonad n a
  pushVec pat (TcMonad m) =
    TcMonad (ReaderT $ \env ->
      runReaderT m
        TcEnv { globals = globals env,
                hints = hints env,
                sourceLocation = sourceLocation env,
                env_scope = extendScope pat (env_scope env),
                env_refinement = shift (size pat) (env_refinement env)
              })

-- | Initial environment
emptyEnv :: TcEnv Z
emptyEnv = TcEnv {
  globals = prelude,
  hints = [],
  sourceLocation = [],
  env_scope = emptyScope,
  env_refinement = emptyR
}

--------------------------------------------------------------------
-- Globals
-- | Find a name's user supplied type signature
lookupHint :: (MonadReader (TcEnv n) m) => GlobalName -> m (Maybe (Typ n))
lookupHint v = do
  hints <- asks hints
  return $ listToMaybe [ weakenClosed ty | (x,ty) <- hints, v == x]

lookupGlobalTy :: GlobalName -> TcMonad n (Typ n)
lookupGlobalTy v = do
    env <- ask
    case [a | ModuleDecl v' a <- globals env, v == v'] of
      [a] -> return (weakenClosed a)
      _   -> do
        mty <- lookupHint v
        case mty of
          Just ty -> return ty
          Nothing -> err [ DS $ "The variable " ++ show v ++ " was not found" ]

lookupGlobalDef :: GlobalName -> TcMonad n (Term n)
lookupGlobalDef v = do
    env <- ask
    case [a | ModuleDef v' a <- globals env, v == v'] of
      [a] -> return (weakenClosed a)
      _  -> err [ DS ("The variable " ++ show v ++ " was not found"),
            DS "(out of scope)"]

-- | Find the datatype declaration of a type constructor in the context
lookupTCon :: TyConName -> TcMonad n DataDef
lookupTCon v = do
  g <- asks globals
  scanGamma g
  where
    scanGamma [] = do
      currentEnv <- asks globals
      err
        [ DS "The type constructor",
          DC v,
          DS "was not found.",
          DS "The current environment is",
          DS (pp currentEnv)
        ]
    scanGamma ((ModuleData n d) : g) =
      if n == v
        then return d
        else scanGamma g
    scanGamma (_ : g) = scanGamma g

-- | Find a data constructor in the context, returns a list of
-- all potential matches
lookupDConAll ::
  DataConName ->
  TcMonad n [(TyConName, ScopedConstructorDef)]
lookupDConAll v = do
  g <- asks globals
  scanGamma g
  where
    scanGamma [] = return []
    scanGamma ((ModuleData tn (DataDef delta _ cs)) : g) =
      case find (\(ConstructorDef v'' _) -> v'' == v) cs of
        Nothing -> scanGamma g
        Just c -> do
          more <- scanGamma g
          return $ (tn,
             ScopedConstructorDef delta c) :  more
    scanGamma (_ : g) = scanGamma g

-- | Given the name of a data constructor and the type that it should
-- construct, find the telescopes for its parameters and arguments.
-- Throws an error if the data constructor cannot be found for that type.
lookupDCon ::
  DataConName ->
  TyConName ->
  TcMonad n ScopedConstructorDef
lookupDCon c tname = do
  matches <- lookupDConAll c
  case lookup tname matches of
    Just scd -> return scd
    Nothing ->
      err
        ( [ DS "Cannot find data constructor",
            DS c,
            DS "for type",
            DC tname,
            DS "Potential matches were:"
          ]
            ++ map (DC . fst) matches
        )

--------------------------------------------------------------------

-- | A local context is an environment that binds n variables (and may also
-- include local definitions).
type Context a = Ctx Term a

weakenDef :: SNat n -> (Fin p, Term p) -> (Fin (n + p), Term (n + p))
weakenDef m (x,y) = (Fin.weakenFin m x, applyE @Term (weakenE' m) y)

emptyContext :: Context N0
emptyContext = emptyC


{-
getLocalCtx :: forall n. SNatI n => TcMonad (Ctx Term n)
getLocalCtx = do
  c <- asks ctx
  case c of
    Context _ (t :: Ctx Term p) _ ->
         case testEquality @_ @n snat (snat :: SNat p) of
           Just Refl -> return t
           Nothing -> err [DS "invalid scope"]

getLocalDefs :: forall n. SNatI n => TcMonad [(Fin n, Term n)]
getLocalDefs = do
  c <- asks ctx
  case c of
    Context _ _ (t :: [(Fin p, Term p)]) ->
         case testEquality @_ @n snat (snat :: SNat p) of
           Just Refl -> return t
           Nothing -> err [DS "invalid scope"]
-}

{-
lookupDef :: Fin m -> Context m n -> TcMonad (Maybe (Term n))
lookupDef x (Context _ _ gamma) = go gamma
    where
      go [] = return Nothing
      go ((y,u):t) = if x == y then return (Just u) else go t
-}

{-
-- | Extend with new definitions
extendDecls :: [(Fin n, Term n)] -> Context m n -> Context m n
extendDecls d c@(Context gamma defs) = Context n gamma (d ++ defs)
-}


-- | Find the type of a local variable in the context
-- This cannot fail
lookupTy :: Fin n -> Context n -> Term n
lookupTy x gamma = applyEnv gamma x

-- | Extend the context with a new declaration
extendTy :: Typ n -> Context n -> Context (S n)
extendTy d gamma = gamma +++ d

extendDef :: Fin n -> Term n -> Context n -> Context n
extendDef d = error "TODO: local definitions unsupported"

extendLocal :: Local p n -> (Context (p + n) -> m a) -> (Context n -> m a)
extendLocal (LocalDecl x t) k ctx = k (extendTy t ctx)
extendLocal (LocalDef x u) k ctx = error "TODO: local definitions unsupported"

--------------------------------------------------------------------
-- Source locations

-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall a n. Display n a => SourcePos -> a -> Scope LocalName n -> SourceLocation

-- | Push a new source position on the location stack.
extendSourceLocation :: (Display n t) => SourcePos -> t -> TcMonad n a -> TcMonad n a
extendSourceLocation p t m = do
  s <- scope
  local (\e@TcEnv {sourceLocation = locs} ->
     e {sourceLocation = SourceLocation p t s : locs}) m

-- | access current source location
getSourceLocation :: MonadReader (TcEnv n) m => m [SourceLocation]
getSourceLocation = asks sourceLocation

--------------------------------------------------------------------
-- Errors

-- | An error that should be reported to the user
data Err = Err [SourceLocation] (Doc ())

instance Semigroup Err where
  (<>) :: Err -> Err -> Err
  (Err src1 d1) <> (Err src2 d2) = Err (src1 ++ src2) (d1 `mappend` d2)

instance Monoid Err where
  mempty :: Err
  mempty = Err [] mempty

--scopedDisplay :: Display n a => a -> Scope LocalName n -> Doc ()
--scopedDisplay a s =
--  display a (namesDI (toList (scope_names s)))

-- | display an error
-- TODO: preserve passed in di for printing the term???
displayErr :: Err -> Doc ()
displayErr (Err [] msg) = msg
displayErr (Err ((SourceLocation p term s) : ss) msg) = scopedDisplay p s <+> nest 2 msg
      <+> nest 2 (pretty "in the expression"
                 <+> nest 2 (scopedDisplay term s))

-- | Print a warning
warn :: [D n] -> TcMonad n ()
warn d = do
  loc <- getSourceLocation
  s <- scope
  liftIO $ putStrLn $ "warning: " ++ show (sep $ map (`scopedDisplay` s) d)

-- | Print an error, making sure that the scope lines up
err :: [D n] -> TcMonad n b
err d = do
  loc <- getSourceLocation
  s <- scope
  throwError $ Err loc (sep $ map (`scopedDisplay` s) d)

-- | Augment an error message with addition information (if thrown)
extendErr :: TcMonad n a -> [D n] -> TcMonad n a
extendErr ma d =
  ma `catchError` \(Err ps msg) -> do
    s <- scope
    let msg' = sep $ map (`scopedDisplay` s) d
    throwError $ Err ps (vcat [msg, msg'])

whenNothing :: Maybe a -> [D n] -> TcMonad n a
whenNothing x msg =
  case x of
     Just r -> return r
     Nothing -> err msg

--------------------------------------------------------------
-- Modules

-- | Add a type hint
extendHints :: (MonadReader (TcEnv n) m) => (GlobalName, Typ Z) -> m a -> m a
extendHints h = local (\m@TcEnv {hints = hs} -> m {hints = h : hs})

-- | Extend the global environment with a new entry
extendCtx :: (MonadReader (TcEnv n) m) => ModuleEntry -> m a -> m a
extendCtx d =
  local (\m@TcEnv{globals = cs} -> m {globals = d : cs})

-- | Extend the context with a list of global bindings
extendCtxs :: (MonadReader (TcEnv n) m) => [ModuleEntry] -> m a -> m a
extendCtxs ds =
  local (\m@TcEnv {globals = cs} -> m {globals = ds ++ cs})

-- | Extend the context with a module
-- Note we must reverse the order
extendCtxMod :: (MonadReader (TcEnv n) m) => Module -> m a -> m a
extendCtxMod m = extendCtxs (reverse $ moduleEntries m)

-- | Extend the context with a list of modules
extendCtxMods :: (MonadReader (TcEnv n) m) => [Module] -> m a -> m a
extendCtxMods mods k = foldr extendCtxMod k mods
