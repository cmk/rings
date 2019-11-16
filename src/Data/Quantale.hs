{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Quantale where

import Data.Connection hiding (floor', ceiling')
import Data.Connection.Yoneda
import Data.Group
import Data.Prd
import Data.Prd.Lattice
import Prelude hiding (negate, until, filter)
import Test.Property.Util ((<==>),(==>))
import qualified Prelude as Pr

residuated :: Quantale a => a -> a -> a -> Bool
residuated x y z = x <> y <~ z <==> y <~ x \\ z <==> x <~ z // y


-- | Residuated, partially ordered semigroups.
--
-- In the interest of usability we abuse terminology slightly and use the
-- term 'quantale' to describe any residuated, partially ordered semigroup. 
-- This admits instances of hoops and triangular (co)-norms.
-- 
-- There are several additional properties that apply when the poset structure
-- is lattice-ordered (i.e. a residuated lattice) or when the semigroup is a 
-- monoid or semiring. See the associated 'Properties' module.

class (Semigroup a, Prd a) => Quantale a where
    residr :: a -> Conn a a
    residr x = Conn (x<>) (x\\)

    residl :: a -> Conn a a
    residl x = Conn (<>x) (//x)

    (\\) :: a -> a -> a
    x \\ y = connr (residr x) y

    (//) :: a -> a -> a
    x // y = connl (residl x) y

incBy :: Yoneda a => Quantale a => a -> Rep a -> Rep a
incBy x = connl filter . (x <>) . connr filter

decBy :: Yoneda a => Quantale a => a -> Rep a -> Rep a
decBy x = connl filter . (x \\) . connr filter
