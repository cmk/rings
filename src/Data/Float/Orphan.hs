-- | Orphan instances from base.
module Data.Float.Orphan where

import Data.Connection.Yoneda
import Data.Group
import Data.Prd.Lattice

import Control.Applicative
import Data.Int
import Data.Float
import Data.Word
import Data.Prd
import Data.Quantale
import Data.Dioid
import Data.Semiring
import Prelude hiding (until)

instance Semigroup Float where
  (<>) = (+)
  {-# INLINE (<>) #-}

instance Monoid Float where
  mempty = 0

instance Quantale Float where
    x \\ y = y // x

    --x <> y <~ z iff y <~ x \\ z iff x <~ z // y.
    y // x | y =~ x = 0
           | otherwise = let z = y - x in if z + x <~ y then upper' z (x<>) y else lower' z (x<>) y 

-- @'lower'' x@ is the least element /y/ in the descending
-- chain such that @not $ f y '<~' x@.
--
lower' :: Prd a => Float -> (Float -> a) -> a -> Float
lower' z f x = until (\y -> f y <~ x) ge (shift $ -1) z

-- @'upper' y@ is the greatest element /x/ in the ascending
-- chain such that @g x '<~' y@.
--
upper' :: Prd a => Float -> (Float -> a) -> a -> Float
upper' z g y = while (\x -> g x <~ y) le (shift 1) z
