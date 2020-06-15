{-# Language Safe                #-}
module Data.Ring.Syntax (
  -- * RebindableSyntax
    fromInteger
  , fromRational
  , type Integer
  , type Rational
) where

import safe Data.Connection (connection)
import safe Data.Connection.Type
import safe Data.Connection.Round
import safe Data.Ring
import Prelude hiding (Num(..), Fractional(..), round)

-- | A monotone function from the integers to /a/.
--
-- This is a lawful replacement for the version in base.
--
fromInteger :: IntegerRing a => Integer -> a
fromInteger = connr connection . Right @()

-- | A lawful replacement for the version in base.
--
-- >>> fromRational @Float 1.3
-- 1.3
-- >>> fromRational @Float (1 :% 0)
-- Infinity
-- >>> fromRational @Float (0 :% 0)
-- NaN
--
fromRational :: RationalField a => Rational -> a
fromRational = round
