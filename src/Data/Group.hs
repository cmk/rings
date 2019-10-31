module Data.Group where

import Prelude hiding (Num(..))

infixl 6 <<

-- |A 'Group' is a 'Monoid' plus a function, 'negate', such that: 
--
-- @a << negate a == mempty@
--
-- @negate a << a == mempty@
--
class Monoid a => Group a where
  {-# MINIMAL (negate | (<<)) #-}

  negate :: a -> a
  negate x = mempty << x

  (<<) :: a -> a -> a
  x << y = x <> negate y
