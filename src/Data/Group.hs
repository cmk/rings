module Data.Group where

import Data.Complex
import Prelude hiding (Num(..))

infixl 6 <<

-- | A 'Group' is a 'Monoid' plus a function, 'negate', such that: 
--
-- @g << negate g ≡ mempty@
--
-- @negate g << g ≡ mempty@
--
class Monoid g => Group g where
  {-# MINIMAL (negate | (<<)) #-}

  negate :: g -> g
  negate x = mempty << x

  (<<) :: g -> g -> g
  x << y = x <> negate y
