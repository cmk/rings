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
  , (/), (\\), (^^)
  , recip
  -- * Fields
  , type FieldLaw, Field, Real
  , ninf
) where

import safe Data.Complex
import safe Data.Fixed
import safe Data.Semiring
import safe Data.Semigroup.Additive 
import safe GHC.Real hiding (Real, Fractional(..), (^^), (^), div)
import safe Numeric.Natural
import safe Foreign.C.Types (CFloat(..),CDouble(..))

import Prelude (Monoid(..) , Float, Double)

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

instance Field a => Semifield (Complex a)


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
