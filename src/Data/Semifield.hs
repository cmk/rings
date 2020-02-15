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
    (/)
  , (\\)
  , (^^)
  , recip
  , anan
  , pinf
  , ninf
  , type SemifieldLaw, Semifield
  , type FieldLaw, Field, Real
) where

import safe Data.Bool
import safe Data.Complex
import safe Data.Fixed
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Int
import safe Data.Semiring
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Semigroup.Additive
import safe Data.Semigroup.Multiplicative 
import safe Data.Tuple
import safe Data.Word
import safe GHC.Real hiding (Real, Fractional(..), (^^), (^), div)
import safe Numeric.Natural
import safe Foreign.C.Types (CFloat(..),CDouble(..))

import Prelude ( Eq(..), Ord(..), Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, fromInteger, Float, Double)
import qualified Prelude as P


infixr 8 \\, ^^

-- @ 'one' '==' a '^^' 0 @
--
-- >>> 8 ^^ 0 :: Double
-- 1.0
-- >>> 8 ^^ 0 :: Pico
-- 1.000000000000
--
(^^) :: (Multiplicative-Group) a => a -> Integer -> a
a ^^ n = unMultiplicative $ greplicate n (Multiplicative a)

(\\) :: (Multiplicative-Group) a => a -> a -> a
(\\) x y = recip x * y

-- | Take the reciprocal of a multiplicative group element.
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

anan :: Semifield a => a
anan = zero / zero
{-# INLINE anan #-}

pinf :: Semifield a => a
pinf = one / zero
{-# INLINE pinf #-}

ninf :: Field a => a
ninf = negate one / zero
{-# INLINE ninf #-}

-- Sometimes called a division ring
type SemifieldLaw a = ((Additive-Monoid) a, (Multiplicative-Group) a)

-- | A semifield, near-field, division ring, or associative division algebra.
--
-- Instances needn't have commutative multiplication or additive inverses.
--
-- See also the wikipedia definitions of < https://en.wikipedia.org/wiki/Semifield semifield >, < https://en.wikipedia.org/wiki/Near-field_(mathematics) near-field >, < https://en.wikipedia.org/wiki/Division_ring division ring >, and < https://en.wikipedia.org/wiki/Division_algebra division algebra >.
-- 
class (Semiring a, SemifieldLaw a) => Semifield a

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

instance Field a => Semifield (Complex a)

type FieldLaw a = ((Additive-Group) a, (Multiplicative-Group) a)

class (Ring a, Semifield a, FieldLaw a) => Field a

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

instance Field a => Field (Complex a)

class Field a => Real a

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
