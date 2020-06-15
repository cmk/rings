{-# Language Safe                #-}
module Data.Semiring.Syntax (
  -- * RebindableSyntax
    fromInteger
  --, fromRational
) where

import safe Control.Category ((>>>))
import safe Data.Connection (connection)
import safe Data.Connection.Int (natint)
import safe Data.Connection.Type
import safe Data.Semiring
import safe Data.Order.Topology
import Prelude hiding (Num(..), Fractional(..), round)

-- | A monotone map from 'Natural' to /a/.
--
-- Maps all negative arguments to 'zero'.
--
fromInteger :: NaturalSemiring a => Integer -> a
fromInteger = connr (connection >>> natint) . Right @()

-- TODO:

-- | A monotone map from 'Ratio Natural' to /a/.
--
-- Maps all negative arguments to 'zero'.
--
--fromRational :: PositiveSemifield a => Rational -> a
--fromRational = undefined
