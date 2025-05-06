{-# LANGUAGE UndecidableSuperClasses #-}

module AutoEnv.DependentScope
  ( Sized (..),
    MonadScoped (..),
    Scope (..),
    ScopedReader (..),
    ScopedReaderT (..),
    LocalName (..),
    empty,
    singleton',
    singleton,
    append',
    append,
    runScopedReader,
    scope,
    scopeSize,
    fromScope,
    withScopeSize,
    mapScope,
    push,
    push1',
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
    env,
    fromVec,
    idE,
    oneE,
    shift1E,
    shiftNE,
    singletonE,
    transform,
    weakenE',
    zeroE,
    (.++),
    (.>>),
  )
import AutoEnv.Lib
import AutoEnv.MonadScoped qualified as SimpleScope
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

-- Note that we could parametrize all subsequent definitions by an initial
-- scope. We instead make the choice of fixing the outer scope to Z. This
-- simplifies all subsequent definition, and working in a latent undefined scope
-- seems exotic and can be emulated fairly easily.
data Scope u s p n = Scope {uscope :: Vec p u, sscope :: Env s p (p + n)}

empty :: Scope u s Z n
empty = Scope Vec.empty zeroE

singleton' :: forall v u s n. (Subst v s) => u -> s n -> Scope u s N1 n
singleton' u v = let v' = applyE (shift1E @v) v in Scope (Vec.singleton u) (oneE @s @(S n) v')

singleton :: forall u s n. (SubstVar s) => u -> s n -> Scope u s N1 n
singleton = singleton' @s

append' :: forall u s pl pr n. (SubstVar s, SNatI pr) => Scope u s pl n -> Scope u s pr (pl + n) -> Scope u s (pr + pl) n
append' (Scope ul sl) (Scope ur sr) = case axiomAssoc @pr @pl @n of Refl -> Scope (Vec.append ur ul) (sl ++++ sr)

append :: forall u s pl pr n. (SubstVar s) => Scope u s pl n -> Scope u s pr (pl + n) -> Scope u s (pr + pl) n
append l r@(Scope ur _) = withSNat (Vec.vlength ur) $ append' @u @s @pl @pr @n l r

nth :: (SubstVar s) => Fin p -> Scope u s p n -> (u, s (p + n))
nth i (Scope u s) = (u Vec.! i, s `applyEnv` i)

map :: (u -> u') -> (forall m. s m -> s' m) -> Scope u s p n -> Scope u' s' p n
map f g (Scope u s) = Scope (Vec.map f u) (transform g s)

-- | Scoped monads provide implicit access to the current scope and a way to
-- extend that scope with a new scope.
class (forall n. Monad (m n), SubstVar s, Shiftable b) => MonadScoped u s b m | m -> u, m -> s, m -> b where
  scope' :: m n (SNat n, Scope u s n Z)
  pushEnv :: (SNatI p) => Scope u s p n -> m (p + n) a -> m n a
  blob :: m n (b n)
  local :: (b n -> b n) -> m n a -> m n a

scope :: forall u s b m n. (MonadScoped u s b m) => m n (Scope u s n Z)
scope = case axiomPlusZ @n of Refl -> snd <$> scope'

scopeSize :: (MonadScoped u s b m) => m n (SNat n)
scopeSize = fst <$> scope'

fromScope :: forall t u s b m n. (MonadScoped u s b m, SubstVar s) => Fin n -> m n (u, s n)
fromScope i = case axiomPlusZ @n of Refl -> nth i <$> scope

withScopeSize :: forall t n u s b m a. (MonadScoped u s b m) => ((SNatI n) => m n a) -> m n a
withScopeSize k = do
  size <- scopeSize
  withSNat size k

-- projectScope :: Scope u s n -> SimpleScope.Scope u n
-- projectScope s = let (k, v) = iter SZ s in SimpleScope.Scope k v
--   where
--     iter :: forall k u s n. SNat k -> Scope u s n -> (SNat (k + n), Vec n u)
--     iter k TNil = case axiomPlusZ @k of Refl -> (k, Vec.empty)
--     iter k (TCons @_ @_ @n' @_ (u, _) xs) =
--       case axiomSus @k @n' of
--         Refl -> let (k', xs') = withSNat k $ iter @(S k) SS xs in (k', u Vec.::: xs')

-- projectScope :: Scope u s n -> Vec n u
-- projectScope TNil = Vec.empty
-- projectScope (TCons @_ @_ @n' @_ (u, _) xs) = u Vec.::: projectScope xs

-----------------------------------------------------------------------
-- ScopedReader monad
-----------------------------------------------------------------------

-- Trivial instance of MonadScoped
type ScopedReader u s b n = ScopedReaderT u s b Identity n

runScopedReader :: forall t n u s b a. (SubstVar s, SNatI n) => SNat n -> Vec n u -> Ctx s n -> b n -> ScopedReader u s b n a -> a
runScopedReader n u s b m = case axiomPlusZ @n of Refl -> runIdentity $ runScopedReaderT m (n, Scope u s, b)

-----------------------------------------------------------------------
-- ScopedReaderT monad transformer
-----------------------------------------------------------------------

-- | A monad transformer that adds a scope environment to any existing monad
-- We also cannot make it an instance of the MonadTrans class because
-- the scope size n needs to be the next-to-last argument instead of the
-- underlying monad
newtype ScopedReaderT u s b m n a = ScopedReaderT {runScopedReaderT :: (SNat n, Scope u s n Z, b n) -> m a}
  deriving (Functor)

-- TODO: should this be moved to MonadScoped's API?
mapScope :: (Monad m) => (u -> u') -> (forall m. s m -> s' m) -> ScopedReaderT u' s' b m n a -> ScopedReaderT u s b m n a
mapScope f g m = ScopedReaderT $ \(k, s, b) ->
  let s' = map f g s
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
  scope' = ScopedReaderT $ \(k, s, _) -> return (k, s)

  -- TODO: what is going when this signature is removed?!?
  pushEnv :: forall m s b p n a. (Monad m, SubstVar s, Shiftable b, SNatI p) => Scope u s p n -> ScopedReaderT u s b m (p + n) a -> ScopedReaderT u s b m n a
  pushEnv (ext :: Scope u s p n) m =
    ScopedReaderT $ \(sn, ss, sb) ->
      let p = snat @p
          sn' = sPlus p sn
          ss' = case axiomPlusZ @n of Refl -> append @_ @_ @_ @_ @Z ss ext
          sb' = shift p sb
       in runScopedReaderT m (sn', ss', sb')
  blob = ScopedReaderT $ \(_, _, b) -> return b
  local f m = ScopedReaderT $ \(k, s, b) -> runScopedReaderT m (k, s, f b)

-----------------------------------------------------------------------
-- Extracting data from binders/patterns
-----------------------------------------------------------------------

-- | Extract data from the pattern. This typeclass should be used when the
-- binders are dependent, i.e. the data associated to a binder can refer to
-- previous binders. If you don't need scoped data, use
-- 'MonadScoped.MonadScoped' instead.
class (Sized p) => WithData (p :: Type) (u :: Type) (s :: Nat -> Type) (n :: Nat) where
  getData :: p -> Scope u s (Size p) n
  getData p = snd $ getSizeData @_ @_ @_ @n p
  getSizeData :: p -> (SNat (Size p), Scope u s (Size p) n)
  getSizeData p = (size p, getData @_ @_ @_ @n p)

instance Sized (Scope u s p n) where
  type Size (Scope u s p n) = p
  size (Scope v _) = Vec.vlength v

instance WithData (Scope u s p n) u s n where
  getData = id
  getSizeData s = (size s, s)

push :: forall u s b m n p a. (MonadScoped u s b m, WithData p u s n) => p -> m (Size p + n) a -> m n a
push p = withSNat (size p) $ pushEnv (getData @p @u @s @n p)

push1' :: forall v u s b m n a. (MonadScoped u s b m, Subst v s) => u -> s n -> m (S n) a -> m n a
push1' u s = pushEnv (singleton' @v u s)

push1 :: forall u s b m n a. (MonadScoped u s b m, SubstVar s) => u -> s n -> m (S n) a -> m n a
push1 = push1' @s

-- pushu :: forall t p u s b n m a. (MonadScoped U1 b m, WithData p u s n) => p -> m (Size p + n) a -> m n a
-- pushu p = pushTelescope (map (\u _ -> (u, U1)) $ getData @_ @u @s p)
pushu :: (MonadScoped u Const b m, SNatI p) => Vec p u -> m (p + n) a -> m n a
-- TODO: remove usage of `env`?
pushu u = pushEnv (Scope u (env $ const Const))

push1u :: (MonadScoped u Const b m) => u -> m (S n) a -> m n a
push1u u = pushEnv (Scope (Vec.singleton u) (env $ const Const))

-- push1u :: (MonadScoped U1 b m) => u -> m (S n) a -> m n a
-- push1u u = pushTelescope (TCons (u, U1) TNil)