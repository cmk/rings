{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Semigroup.Quantale where

import Data.Connection hiding (floor', ceiling')
import Data.Connection.Yoneda
import Data.Float
import Data.Group
import Data.Prd
import Data.Prd.Lattice
import Data.Word
import Data.Semigroup.Orphan ()
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

incBy :: Yoneda a => Quantale a => a -> Rep a -> Rep a
incBy x = connl filter . (x <>) . connr filter

decBy :: Yoneda a => Quantale a => a -> Rep a -> Rep a
decBy x = connl filter . (x \\) . connr filter
