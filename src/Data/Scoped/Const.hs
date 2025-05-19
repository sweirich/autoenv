module Data.Scoped.Const where

import AutoEnv (Subst(..), SubstVar(..), Shiftable(..))

data Const n = Const

instance SubstVar Const where
  var _ = Const

instance Shiftable Const where
  shift _ _ = Const

instance (SubstVar a) => Subst a Const where
  applyE _ _ = Const
