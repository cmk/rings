{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}

module Data.Semifield (
  -- * Semifields
    type SemifieldLaw, Semifield
  , anan, pinf
  , (/), (\\)
  , recip
  -- * Fields
  , type FieldLaw, Field, Real
  , ninf
  , (^^)
) where

import safe Data.Fixed
import safe Data.Semiring
import safe GHC.Real hiding (Real, Fractional(..), (^^), (^), div)
import safe Numeric.Natural
import safe Foreign.C.Types (CFloat(..),CDouble(..))

import Prelude (Monoid(..), Integer, Float, Double, ($))

-------------------------------------------------------------------------------
-- Semifields
-------------------------------------------------------------------------------

type SemifieldLaw a = ((Additive-Monoid) a, (Multiplicative-Group) a)

-- | A semifield, near-field, or division ring.
--
-- Instances needn't have commutative multiplication or additive inverses,
-- however addition must be commutative, and addition and multiplication must 
-- be associative as usual.
--
-- See also the wikipedia definitions of:
--
-- * < https://en.wikipedia.org/wiki/Semifield semifield >
-- * < https://en.wikipedia.org/wiki/Near-field_(mathematics) near-field >
-- * < https://en.wikipedia.org/wiki/Division_ring division ring >
-- 
class (Semiring a, SemifieldLaw a) => Semifield a

-- | The /NaN/ value of the semifield.
--
-- @ 'anan' = 'zero' '/' 'zero' @
--
anan :: Semifield a => a
anan = zero / zero
{-# INLINE anan #-}

-- | The positive infinity of the semifield.
--
-- @ 'pinf' = 'one' '/' 'zero' @
--
pinf :: Semifield a => a
pinf = one / zero
{-# INLINE pinf #-}

infixl 7 \\, /

-- | Reciprocal of a multiplicative group element.
--
-- @ 
-- x '/' y = x '*' 'recip' y
-- x '\\' y = 'recip' x '*' y
-- @
--
-- >>> recip (3 :+ 4) :: Complex Rational
-- 3 % 25 :+ (-4) % 25
-- >>> recip (3 :+ 4) :: Complex Double
-- 0.12 :+ (-0.16)
-- >>> recip (3 :+ 4) :: Complex Pico
-- 0.120000000000 :+ -0.160000000000
-- 
recip :: (Multiplicative-Group) a => a -> a 
recip a = one / a
{-# INLINE recip #-}

-- | Right division by a multiplicative group element.
--
(/) :: (Multiplicative-Group) a => a -> a -> a
a / b = unMultiplicative (Multiplicative a << Multiplicative b)
{-# INLINE (/) #-}

-- | Left division by a multiplicative group element.
--
-- When '*' is commutative we must have:
--
-- @ x '\\' y = y '/' x @
--
(\\) :: (Multiplicative-Group) a => a -> a -> a
(\\) x y = recip x * y

-------------------------------------------------------------------------------
-- Fields
-------------------------------------------------------------------------------

type FieldLaw a = ((Additive-Group) a, (Multiplicative-Group) a)

-- | A < https://en.wikipedia.org/wiki/Field_(mathematics) field >.
--
class (Ring a, Semifield a, FieldLaw a) => Field a

-- | A type modeling the real numbers.
--
class Field a => Real a

-- | The 'one' '/' 'zero' value of the field.
--
-- @ 'ninf' = 'negate' 'one' '/' 'zero' @
--
ninf :: Field a => a
ninf = negate one / zero
{-# INLINE ninf #-}

infixr 8 ^^

-- | Integral power of a multiplicative group element.
--
-- @ 'one' '==' a '^^' 0 @
--
-- >>> 8 ^^ 0 :: Double
-- 1.0
-- >>> 8 ^^ 0 :: Pico
-- 1.000000000000
--
(^^) :: (Multiplicative-Group) a => a -> Integer -> a
a ^^ n = unMultiplicative $ greplicate n (Multiplicative a)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semifield ()
instance Semifield (Ratio Natural)
instance Semifield Rational

instance Semifield Uni
instance Semifield Deci
instance Semifield Centi
instance Semifield Milli
instance Semifield Micro
instance Semifield Nano
instance Semifield Pico

instance Semifield Float
instance Semifield Double
instance Semifield CFloat
instance Semifield CDouble

--instance Field a => Semifield (Complex a)


instance Field ()
instance Field Rational

instance Field Uni
instance Field Deci
instance Field Centi
instance Field Milli
instance Field Micro
instance Field Nano
instance Field Pico

instance Field Float
instance Field Double
instance Field CFloat
instance Field CDouble

--instance Field a => Field (Complex a)



instance Real Rational

instance Real Uni
instance Real Deci
instance Real Centi
instance Real Milli
instance Real Micro
instance Real Nano
instance Real Pico

instance Real Float
instance Real Double
instance Real CFloat
instance Real CDouble
