{-# LANGUAGE CPP  #-}
{-# LANGUAGE Safe #-}

module Data.Group where

import safe Data.Complex
import safe Data.Fixed
import safe Data.Int
import safe Data.Complex
import safe Data.Semiring
import safe GHC.Real

import safe Prelude hiding (Num(..))
import safe qualified Prelude as N

infixl 6 <<

-- | A 'Group' is a 'Monoid' plus a function, 'negate', such that: 
--
-- @g << negate g ≡ mempty@
--
-- @negate g << g ≡ mempty@
--
class Monoid a => Group a where
  {-# MINIMAL (negate | (<<)) #-}

  negate :: a -> a
  negate x = mempty << x

  (<<) :: a -> a -> a
  x << y = x <> negate y

instance Group () where
  negate () = ()

instance (Group a, Semiring a) => Group (Ratio a) where
  negate (x :% y) = negate x :% y

instance Group a => Group (Complex a) where
  negate (x1 :+ y1) = negate x1 :+ negate y1
  {-# INLINE negate #-}

instance (Group a, Semiring a) => Semiring (Complex a) where
  (x1 :+ y1) >< (x2 :+ y2) = (x1 >< x2 << y1 >< y2) :+ (x1 >< y2 <> y1 >< x2)
  {-# INLINE (><) #-}

  fromBoolean False = mempty
  fromBoolean True = fromBoolean True :+ mempty
  {-# INLINE fromBoolean #-}

#define deriveGroup(ty)            \
instance Group (ty) where {        \
   (<<) = (N.-)                    \
;  negate = N.negate               \
;  {-# INLINE (<<) #-}             \
;  {-# INLINE negate #-}           \
}

deriveGroup(Int)
deriveGroup(Int8)
deriveGroup(Int16)
deriveGroup(Int32)
deriveGroup(Int64)
deriveGroup(Integer)

deriveGroup(Uni)
deriveGroup(Deci)
deriveGroup(Centi)
deriveGroup(Milli)
deriveGroup(Micro)
deriveGroup(Nano)
deriveGroup(Pico)
