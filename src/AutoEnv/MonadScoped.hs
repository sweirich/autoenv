{-# LANGUAGE UndecidableSuperClasses #-}

module AutoEnv.MonadScoped
  ( Sized (..),
    MonadScoped (..),
    ScopedReader (..),
    ScopedReaderT (..),
    LocalName (..),
    runScopedReader,
    scope,
    scopeSize,
    get,
    withScopeSize,
    transform,
    push,
    push1,
    WithData (..),
    pushu,
    push1u,
  )
where

import AutoEnv.Classes (Sized (..))
import AutoEnv.Context
import AutoEnv.Env
  ( Env,
    Shiftable (..),
    Subst (..),
    SubstVar,
    applyEnv,
    fromVec,
    idE,
    oneE,
    shift1E,
    shiftNE,
    singletonE,
    weakenE',
    zeroE,
    (.++),
    (.:),
    (.>>),
  )
import AutoEnv.Lib
import AutoEnv.Scope (Scope (Scope))
import AutoEnv.Scope qualified as Scope
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Reader (MonadReader (ask, local))
import Control.Monad.Writer (MonadWriter (..))
import Data.SNat qualified as SNat
import Data.Scoped.Const (Const (..))
import Data.Vec qualified as Vec
import Prelude hiding (map)

-----------------------------------------------------------------------
-- MonadScoped class
-----------------------------------------------------------------------

-- | Scoped monads provide implicit access to the current scope and a way to
-- extend that scope with a new scope.
class (forall n. Monad (m n), SubstVar s, Shiftable b) => MonadScoped u s b m | m -> u, m -> s, m -> b where
  sizedScope :: m n (SNat n, Scope u s n Z)
  pushScope :: (SNatI p) => Scope u s p n -> m (p + n) a -> m n a
  flatData :: m n (b n)
  local :: (b n -> b n) -> m n a -> m n a

scope :: forall u s b m n. (MonadScoped u s b m) => m n (Scope u s n Z)
scope = case axiomPlusZ @n of Refl -> snd <$> sizedScope

scopeSize :: (MonadScoped u s b m) => m n (SNat n)
scopeSize = fst <$> sizedScope

get :: forall t u s b m n. (MonadScoped u s b m, SubstVar s) => Fin n -> m n (u, s n)
get i = case axiomPlusZ @n of Refl -> Scope.nth i <$> scope

withScopeSize :: forall t n u s b m a. (MonadScoped u s b m) => ((SNatI n) => m n a) -> m n a
withScopeSize k = do
  size <- scopeSize
  withSNat size k

-----------------------------------------------------------------------
-- ScopedReader monad
-----------------------------------------------------------------------

-- Trivial instance of MonadScoped
type ScopedReader u s b n = ScopedReaderT u s b Identity n

runScopedReader ::
  forall t n u s b a.
  (SubstVar s, SNatI n) =>
  SNat n ->
  Vec n u ->
  Ctx s n ->
  b n ->
  ScopedReader u s b n a ->
  a
runScopedReader n u s b m =
  case axiomPlusZ @n of Refl -> runIdentity $ runScopedReaderT m (n, Scope u s, b)

-----------------------------------------------------------------------
-- ScopedReaderT monad transformer
-----------------------------------------------------------------------

-- | A monad transformer that adds a scope environment to any existing monad
-- We also cannot make it an instance of the MonadTrans class because
-- the scope size n needs to be the next-to-last argument instead of the
-- underlying monad
newtype ScopedReaderT u s b m n a = ScopedReaderT {runScopedReaderT :: (SNat n, Scope u s n Z, b n) -> m a}
  deriving (Functor)

-- TODO: should this be (somehow) moved to MonadScoped's API?
transform ::
  (Monad m) =>
  (u -> u') ->
  (forall m. s m -> s' m) ->
  ScopedReaderT u' s' b m n a ->
  ScopedReaderT u s b m n a
transform f g m = ScopedReaderT $ \(k, s, b) ->
  let s' = Scope.transform f g s
   in runScopedReaderT m (k, s', b)

instance (Applicative m) => Applicative (ScopedReaderT u s b m n) where
  pure f = ScopedReaderT $ \x -> pure f
  ScopedReaderT f <*> ScopedReaderT x = ScopedReaderT (\e -> f e <*> x e)

instance (Monad m) => Monad (ScopedReaderT u s b m n) where
  ScopedReaderT m >>= k = ScopedReaderT $ \e ->
    m e >>= (\v -> let x = k v in runScopedReaderT x e)

-- TODO: Disabled due to name clash...
-- instance (MonadReader e m) => MonadReader e (ScopedReaderT t u s b m n) where
--   ask = ScopedReaderT $ const ask
--   local f m = ScopedReaderT (local f . runScopedReaderT m)

instance (MonadError e m) => MonadError e (ScopedReaderT u s b m n) where
  throwError e = ScopedReaderT $ const (throwError e)
  catchError m k = ScopedReaderT $ \s -> runScopedReaderT m s `catchError` (\err -> runScopedReaderT (k err) s)

instance (MonadWriter w m) => MonadWriter w (ScopedReaderT u s b m n) where
  writer w = ScopedReaderT $ const (writer w)
  listen m = ScopedReaderT $ \s -> listen $ runScopedReaderT m s
  pass m = ScopedReaderT $ \s -> pass $ runScopedReaderT m s

instance (Monad m, SubstVar s, Shiftable b) => MonadScoped u s b (ScopedReaderT u s b m) where
  sizedScope = ScopedReaderT $ \(k, s, _) -> return (k, s)

  -- TODO: what is going when this signature is removed?!?
  pushScope :: forall m s b p n a. (Monad m, SubstVar s, Shiftable b, SNatI p) => Scope u s p n -> ScopedReaderT u s b m (p + n) a -> ScopedReaderT u s b m n a
  pushScope (ext :: Scope u s p n) m =
    ScopedReaderT $ \(sn, ss, sb) ->
      let p = snat @p
          sn' = sPlus p sn
          ss' = case axiomPlusZ @n of Refl -> Scope.append @Z ss ext
          sb' = shift p sb
       in runScopedReaderT m (sn', ss', sb')
  flatData = ScopedReaderT $ \(_, _, b) -> return b
  local f m = ScopedReaderT $ \(k, s, b) -> runScopedReaderT m (k, s, f b)

-----------------------------------------------------------------------
-- Extracting data from binders/patterns
-----------------------------------------------------------------------

-- | Extract data from the pattern.
class (Sized p) => WithData (n :: Nat) (p :: Type) (u :: Type) (s :: Nat -> Type) where
  -- The scope size (n) being the first parameter is odd, since it is usually
  -- the last, but since it is the type parameter one usually needs to provide
  -- manually, it has to be first for this to be practical.
  getData :: p -> Scope u s (Size p) n
  getData p = snd $ getSizedData @n p
  getSizedData :: p -> (SNat (Size p), Scope u s (Size p) n)
  getSizedData p = (size p, getData @n p)

instance Sized (Scope u s p n) where
  type Size (Scope u s p n) = p
  size (Scope v _) = Vec.vlength v

instance WithData n (Scope u s p n) u s where
  getData = id
  getSizedData s = (size s, s)

push :: forall u s b m n p a. (MonadScoped u s b m, WithData n p u s) => p -> m (Size p + n) a -> m n a
push p = withSNat (size p) $ pushScope (getData @n p)

push1 :: forall u s b m n a. (MonadScoped u s b m, SubstVar s) => u -> s n -> m (S n) a -> m n a
push1 u s = pushScope (Scope.singleton u s)

pushu :: forall u b m n p a. (MonadScoped u Const b m, SNatI p) => Vec p u -> m (p + n) a -> m n a
pushu u = pushScope (Scope u mkEnv)
  where
    mkEnv :: forall p. (SNatI p) => Env Const p (p + n)
    mkEnv = case snat @p of
      SZ -> zeroE
      SS -> Const .: (shift1E .>> mkEnv)

push1u :: (MonadScoped u Const b m) => u -> m (S n) a -> m n a
push1u u = pushu $ Vec.singleton u