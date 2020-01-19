{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE TypeOperators              #-}

module Data.Group (
    Semigroup(..)
  , mreplicate
  , Quasigroup(..)
  , Loop(..)
  , Group(..)
) where

import safe Data.Magma
import safe Data.Semigroup
import safe Data.Complex
import safe Data.Fixed
import safe Data.Int
import safe Data.Word
import safe GHC.Real
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe Numeric.Natural

import safe Prelude hiding (Num(..))
import safe qualified Prelude as P


--  x << y = x <> inv y
--  inv x = mempty << x
class (Loop a, Monoid a) => Group a where

  inv :: a -> a
  inv x = mempty << x

  greplicate :: Integer -> a -> a
  greplicate n a     
      | n == 0 = mempty
      | n > 0 = mreplicate (P.fromInteger n) a
      | otherwise = mreplicate (P.fromInteger $ P.abs n) (inv a)

instance (Semigroup a, Quasigroup (Maybe a)) => Group (Maybe a) where

-- (<<) has the < https://en.wikipedia.org/wiki/Latin_square_property >.
-- The unique solutions to these equations are written x = a \\ b and y = b // a. The operations '\\' and '//' are called, respectively, left and right division. 

-- https://en.wikipedia.org/wiki/Quasigroup
-- in a group (//) = (\\) = (<>)
class Magma a => Quasigroup a where
  (//) :: a -> a -> a
  default (//) :: Semigroup a => a -> a -> a
  (//) = (<>)

  (\\) :: a -> a -> a
  default (\\) :: Semigroup a => a -> a -> a
  (\\) = (<>)


{-
Every group is a loop, because a ∗ x = b if and only if x = a−1 ∗ b, and y ∗ a = b if and only if y = b ∗ a−1.
The integers Z with subtraction (−) form a quasigroup.
The nonzero rationals Q× (or the nonzero reals R×) with division (÷) form a quasigroup.
https://en.wikipedia.org/wiki/Mathematics_of_Sudoku#Sudokus_from_group_tables
-}
class Quasigroup a => Loop a where

  lempty :: a
  default lempty :: Monoid a => a
  lempty = mempty

  lreplicate :: Natural -> a -> a
  default lreplicate :: Group a => Natural -> a -> a
  lreplicate n = mreplicate n . inv

instance (Semigroup a, Quasigroup (Maybe a)) => Loop (Maybe a)

-- | A generalization of 'Data.List.replicate' to an arbitrary 'Monoid'. 
--
-- Adapted from <http://augustss.blogspot.com/2008/07/lost-and-found-if-i-write-108-in.html>.
--
mreplicate :: Monoid a => Natural -> a -> a
mreplicate n a
    | n == 0 = mempty
    | otherwise = f a n
    where
        f x y 
            | even y = f (x <> x) (y `quot` 2)
            | y == 1 = x
            | otherwise = g (x <> x) ((y P.- 1) `quot` 2) x
        g x y z 
            | even y = g (x <> x) (y `quot` 2) z
            | y == 1 = x <> z
            | otherwise = g (x <> x) ((y P.- 1) `quot` 2) (x <> z)
{-# INLINE mreplicate #-}

{-
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
-}
