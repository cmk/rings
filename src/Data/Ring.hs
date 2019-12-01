module Data.Ring (
    (<<)
  , (><)
  , (<>)
  , negate
  , Ring(..)
) where

import Data.Group
import Data.Semiring
import Prelude hiding (Num(..))

class (Group a, Semiring a) => Ring a where
  {-# MINIMAL abs, signum #-}
  abs :: a -> a

  signum :: a -> a -- satisfies trichotomy law
