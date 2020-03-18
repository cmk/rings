{-# LANGUAGE CPP                        #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}

module Data.Semifield where
{- (
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
-}
import Data.Fixed
import Data.Semiring
import GHC.Real hiding (Real, Fractional(..), (^^), (^), div)
import Numeric.Natural
import Foreign.C.Types (CFloat(..),CDouble(..))

import Prelude (Monoid(..), Integer, Float, Double, ($))



{-
--nanfld :: Prd a => Field a => Trip (Nan a) a
-- Field a => Field (Nan a)
-- /Caution/ this is only legal if (Nan a) has no nans.
{-
fldnan :: Prd a => Field a => Trip a (Nan a)
fldnan = Trip f g f where
  f a = if a =~ 0 / 0 then Nan else Def a 
  g = nan (0 / 0) id
-}

fldord :: Prd a => Field a => Trip a (Nan Ordering)
fldord = Trip f g h where
  g (Def GT) = pinf 
  g (Def LT) = ninf 
  g (Def EQ) = 0
  g Nan = anan 
  
  f x | x =~ anan  = Nan
      | x =~ ninf  = Def LT
      | x <= 0  = Def EQ
      | otherwise  = Def GT

  h x | x =~ anan  = Nan
      | x =~ pinf  = Def GT
      | x >= 0  = Def EQ
      | otherwise  = Def LT

finite :: Prd a => Floating a => a -> Bool
finite a = (a /~ 0/0) || (a /~ pinf) || (a /~ ninf)

extend :: (Prd a, Field a, Field b) => (a -> b) -> a -> b
extend f x  | x =~ 0/0 = 0/0
            | x =~ ninf = ninf
            | x =~ pinf = pinf
            | otherwise = f x

-- | Exception-safe polymorphic infinity.
--
pinf :: Semifield a => a
pinf = 1 / 0

-- | Exception-safe polymorphic negative infinity.
--
ninf :: Field a => a
ninf = (-1) / 0

-- | Exception-safe polymorphic NaN.
--
anan :: Semifield a => a
anan = 0 / 0

-------------------------------------------------------------------------------
-- Semifields
-------------------------------------------------------------------------------

type SemifieldLaw a = ((Additive-Monoid) a, (Multiplicative-Group) a)

-- | The /NaN/ value of a semifield.
--
pattern NaN :: Semifield a => Eq a => a
pattern NaN <- ((== NaN) -> True)
  where NaN = zero / zero

pattern PInf :: Semifield a => Eq a => a
pattern PInf <- ((== pinf) -> True)
  where PInf = one / zero

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
-}
