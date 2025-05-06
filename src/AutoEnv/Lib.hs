-- imports and reexports libraries for Nat / Fin / Vec
module AutoEnv.Lib
  ( module Data.Nat,
    module Data.SNat,
    type Type,
    module Data.Type.Equality,
    SNat (..),
    Nat (..),
    Fin (..),
    Vec (..),
    ToInt (..),
    module Data.LocalName,
  )
where

import Data.Fin (Fin (..))
import Data.Kind (Type)
import Data.LocalName
import Data.Nat
import Data.SNat
import Data.Type.Equality
import Data.Vec (Vec (..))
