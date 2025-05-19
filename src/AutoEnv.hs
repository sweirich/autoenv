-- |
-- Module      : AutoEnv
-- Description : Explicit substitutions
-- Stability   : experimental
module AutoEnv
  (module AutoEnv.Classes,
   module AutoEnv.Env,
   module AutoEnv.MonadNamed,
   module AutoEnv.Lib,
   module AutoEnv.Context,
   Generic(..),
   Generic1(..))
where

import Data.SNat (Nat(..))
import Data.Fin
import Data.Vec (Vec(..))

import AutoEnv.Classes
import AutoEnv.Context
import AutoEnv.Env
import AutoEnv.Lib
import AutoEnv.MonadNamed
import GHC.Generics hiding (S)


