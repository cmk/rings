{-# LANGUAGE CPP  #-}
{-# LANGUAGE Safe #-}

module Data.Group (
    Group(..)
  , Semigroup(..)
) where

import safe Data.Semigroup
import safe Data.Complex
import safe Data.Fixed
import safe Data.Int
import safe Data.Word
import safe GHC.Real
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe Numeric.Natural

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

instance Group a => Group (Complex a) where
  negate (x1 :+ y1) = negate x1 :+ negate y1
  {-# INLINE negate #-}

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

---------------------------------------------------------------------
-- Instances (orphans)
---------------------------------------------------------------------

instance Semigroup Bool where
  (<>) = (||)
  {-# INLINE (<>) #-}

instance Monoid Bool where mempty = False

instance Semigroup a => Semigroup (Complex a) where
  (x1 :+ y1) <> (x2 :+ y2) = (x1 <> x2) :+ (y1 <> y2)
  {-# INLINE (<>) #-}

instance Monoid a => Monoid (Complex a) where
  mempty = mempty :+ mempty

#define deriveSemigroup(ty)        \
instance Semigroup (ty) where {    \
   (<>) = (N.+)                    \
;  {-# INLINE (<>) #-}             \
}

#define deriveMonoid(ty)           \
instance Monoid (ty) where {       \
   mempty = 0                      \
}

deriveSemigroup(Word)
deriveSemigroup(Word8)
deriveSemigroup(Word16)
deriveSemigroup(Word32)
deriveSemigroup(Word64)
deriveSemigroup(Natural)

deriveMonoid(Word)
deriveMonoid(Word8)
deriveMonoid(Word16)
deriveMonoid(Word32)
deriveMonoid(Word64)
deriveMonoid(Natural)

deriveSemigroup(Int)
deriveSemigroup(Int8)
deriveSemigroup(Int16)
deriveSemigroup(Int32)
deriveSemigroup(Int64)
deriveSemigroup(Integer)

deriveMonoid(Int)
deriveMonoid(Int8)
deriveMonoid(Int16)
deriveMonoid(Int32)
deriveMonoid(Int64)
deriveMonoid(Integer)

deriveSemigroup(Uni)
deriveSemigroup(Deci)
deriveSemigroup(Centi)
deriveSemigroup(Milli)
deriveSemigroup(Micro)
deriveSemigroup(Nano)
deriveSemigroup(Pico)

deriveMonoid(Uni)
deriveMonoid(Deci)
deriveMonoid(Centi)
deriveMonoid(Milli)
deriveMonoid(Micro)
deriveMonoid(Nano)
deriveMonoid(Pico)

deriveSemigroup(Float)
deriveSemigroup(CFloat)
deriveMonoid(Float)
deriveMonoid(CFloat)

deriveSemigroup(Double)
deriveSemigroup(CDouble)
deriveMonoid(Double)
deriveMonoid(CDouble)
