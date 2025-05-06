module Data.Vec
  ( module Data.Vec.Lazy,
    vlength,
    append,
    setAt,
  )
where

--- replace with
-- https://hackage.haskell.org/package/fin
-- https://hackage.haskell.org/package/vec

-- Library for length-indexed lists
-- Should be imported qualified as it includes operations that
-- conflict with list operations in the Prelude

import Data.Fin (Fin (..))
import Data.Fin qualified
import Data.Nat
import Data.SNat
import Data.Type.Equality
import Data.Vec.Lazy
import Test.QuickCheck
import Prelude hiding (lookup, repeat, zipWith)

-----------------------------------------------------
-- Vectors (additional definitions)
-----------------------------------------------------

setAt :: Fin n -> Vec n a -> a -> Vec n a
setAt FZ (_ ::: vs) w = w ::: vs
setAt (FS x) (w1 ::: env) w2 = w1 ::: setAt x env w2

append :: forall n m a. Vec n a -> Vec m a -> Vec (n + m) a
append = (Data.Vec.Lazy.++)

lookup :: Fin n -> Vec n a -> a
lookup = flip (!)

vlength :: Vec n a -> SNat n
vlength VNil = SZ
vlength (_ ::: v) = withSNat (vlength v) SS
