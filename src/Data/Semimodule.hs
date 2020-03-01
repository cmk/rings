{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Semimodule (
  -- * Types
    type (**) 
  , type (++) 
  , type Free
  , type Base
  , type FreeModule 
  , type FreeSemimodule
  -- * Left modules
  , type LeftModule
  , LeftSemimodule(..)
  , (*.)
  , (/.)
  , (\.)
  , lerp
  , lscaleDef
  , negateDef
  -- * Right modules
  , type RightModule
  , RightSemimodule(..)
  , (.*)
  , (./)
  , (.\)
  , rscaleDef
  -- * Bimodules
  , type Bimodule
  , Bisemimodule(..)
) where

import safe Data.Complex
import safe Data.Fixed
import safe Data.Functor.Rep
import safe Data.Functor.Compose
import safe Data.Functor.Contravariant
import safe Data.Functor.Product
import safe Data.Int
import safe Data.Semifield
import safe Data.Semiring
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Real hiding (Fractional(..))
import safe Numeric.Natural
import safe Prelude (fromInteger)
import safe Prelude hiding (Num(..), Fractional(..), sum, product)

infixr 2 **
infixr 1 ++

-- | A tensor product of semimodule morphisms.
--
type (f ** g) = Compose f g

-- | A direct sum of free semimodule elements.
--
type (f ++ g) = Product f g

type Free = Representable

type Base f = Rep f

type FreeModule a f = (Free f, (Additive-Group) (f a), Bimodule a a (f a))

type FreeSemimodule a f = (Free f, Bisemimodule a a (f a))

-------------------------------------------------------------------------------
-- Left modules
-------------------------------------------------------------------------------

type LeftModule l a = (Ring l, (Additive-Group) a, LeftSemimodule l a)

-- | < https://en.wikipedia.org/wiki/Semimodule Left semimodule > over a commutative semiring.
--
-- All instances must satisfy the following identities:
-- 
-- @
-- 'lscale' s (x '+' y) = 'lscale' s x '+' 'lscale' s y
-- 'lscale' (s1 '+' s2) x = 'lscale' s1 x '+' 'lscale' s2 x
-- 'lscale' (s1 '*' s2) = 'lscale' s1 . 'lscale' s2
-- 'lscale' 'zero' = 'zero'
-- @
--
-- When the ring of coefficients /s/ is unital we must additionally have:
-- @
-- 'lscale' 'one' = 'id'
-- @
-- 
-- See the properties module for a detailed specification of the laws.
--
class (Semiring l, (Additive-Monoid) a) => LeftSemimodule l a where
  -- | Left-multiply by a scalar.
  --
  lscale :: l -> a -> a


infixr 7 *., \., /. 

-- | Left-multiply a module element by a scalar.
--
(*.) :: LeftSemimodule l a => l -> a -> a
(*.) = lscale

-- | Right-divide a vector by a scalar (on the left).
--
(/.) :: Semifield a => Functor f => a -> f a -> f a
a /. f = (/ a) <$> f

-- | Left-divide a vector by a scalar.
--
(\.) :: Semifield a => Functor f => a -> f a -> f a
a \. f = (a \\)  <$> f

-- | Linearly interpolate between two vectors.
--
-- >>> u = V3 (1 :% 1) (2 :% 1) (3 :% 1) :: V3 Rational
-- >>> v = V3 (2 :% 1) (4 :% 1) (6 :% 1) :: V3 Rational
-- >>> r = 1 :% 2 :: Rational
-- >>> lerp r u v
-- V3 (6 % 4) (12 % 4) (18 % 4)
--
lerp :: LeftModule r a => r -> a -> a -> a
lerp r f g = r *. f + (one - r) *. g

-- | Default definition of 'lscale' for a free module.
--
lscaleDef :: Semiring a => Functor f => a -> f a -> f a
lscaleDef a f = (a *) <$> f

-- | Default definition of '<<' for a commutative group.
--
negateDef :: LeftModule Integer a => a -> a
negateDef a = (-1 :: Integer) *. a

-------------------------------------------------------------------------------
-- Right modules
-------------------------------------------------------------------------------

type RightModule r a = (Ring r, (Additive-Group) a, RightSemimodule r a)

-- | < https://en.wikipedia.org/wiki/Semimodule Right semimodule > over a commutative semiring.
--
-- The laws for right semimodules are analagous to those of left semimodules.
--
-- See the properties module for a detailed specification.
--
class (Semiring r, (Additive-Monoid) a) => RightSemimodule r a where

  -- | Right-multiply by a scalar.
  --
  rscale :: r -> a -> a

infixl 7 .*, .\, ./

-- | Right-multiply a module element by a scalar.
--
(.*) :: RightSemimodule r a => a -> r -> a
(.*) = flip rscale

-- | Right-divide a vector by a scalar.
--
(./) :: Semifield a => Functor f => f a -> a -> f a
(./) = flip (/.)

-- | Left-divide a vector by a scalar (on the right).
--
(.\) :: Semifield a => Functor f => f a -> a -> f a
(.\) = flip (\.)

-- | Default definition of 'rscale' for a free module.
--
rscaleDef :: Semiring a => Functor f => a -> f a -> f a
rscaleDef a f = (* a) <$> f

-------------------------------------------------------------------------------
-- Bimodules
-------------------------------------------------------------------------------

type Bimodule l r a = (LeftModule l a, RightModule r a, Bisemimodule l r a)

-- | < https://en.wikipedia.org/wiki/Bimodule Bisemimodule > over a commutative semiring.
--
-- @
-- 'lscale' l . 'rscale' r = 'rscale' r . 'lscale' l
-- @
--
class (LeftSemimodule l a, RightSemimodule r a) => Bisemimodule l r a where

  -- | Left and right-multiply by two scalars.
  --
  discale :: l -> r -> a -> a
  discale l r = lscale l . rscale r

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semiring l => LeftSemimodule l () where 
  lscale _ = const ()

instance (Additive-Monoid) a => LeftSemimodule () a where 
  lscale _ = id

instance (Additive-Monoid) a => LeftSemimodule Natural a where
  lscale l a = unAdditive $ mreplicate l (Additive a)

instance ((Additive-Monoid) a, (Additive-Group) a) => LeftSemimodule Integer a where
  lscale l a = unAdditive $ greplicate l (Additive a)

instance LeftSemimodule l a => LeftSemimodule l (e -> a) where 
  lscale l = fmap (l *.)

instance LeftSemimodule l a => LeftSemimodule l (Op a e) where 
  lscale l (Op f) = Op $ fmap (l *.) f

instance (LeftSemimodule l a, LeftSemimodule l b) => LeftSemimodule l (a, b) where
  lscale n (a, b) = (n *. a, n *. b)

instance (LeftSemimodule l a, LeftSemimodule l b, LeftSemimodule l c) => LeftSemimodule l (a, b, c) where
  lscale n (a, b, c) = (n *. a, n *. b, n *. c)

instance Semiring a => LeftSemimodule a (Ratio a) where 
  lscale l (x :% y) = (l * x) :% y

instance Ring a => LeftSemimodule a (Complex a) where 
  lscale l (x :+ y) = (l * x) :+ (l * y)

--instance Ring a => LeftSemimodule (Complex a) (Complex a) where 
--   lscale = (*)  

#define deriveLeftSemimodule(ty)                      \
instance LeftSemimodule ty ty where {                 \
   lscale = (*)                                       \
;  {-# INLINE lscale #-}                              \
}

deriveLeftSemimodule(Bool)
deriveLeftSemimodule(Int)
deriveLeftSemimodule(Int8)
deriveLeftSemimodule(Int16)
deriveLeftSemimodule(Int32)
deriveLeftSemimodule(Int64)
deriveLeftSemimodule(Word)
deriveLeftSemimodule(Word8)
deriveLeftSemimodule(Word16)
deriveLeftSemimodule(Word32)
deriveLeftSemimodule(Word64)
deriveLeftSemimodule(Uni)
deriveLeftSemimodule(Deci)
deriveLeftSemimodule(Centi)
deriveLeftSemimodule(Milli)
deriveLeftSemimodule(Micro)
deriveLeftSemimodule(Nano)
deriveLeftSemimodule(Pico)
deriveLeftSemimodule(Float)
deriveLeftSemimodule(Double)
deriveLeftSemimodule(CFloat)
deriveLeftSemimodule(CDouble)
deriveLeftSemimodule((Ratio Integer))
deriveLeftSemimodule((Ratio Natural))

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semiring r => RightSemimodule r () where 
  rscale _ = const ()

instance (Additive-Monoid) a => RightSemimodule () a where 
  rscale _ = id

instance (Additive-Monoid) a => RightSemimodule Natural a where
  rscale r a = unAdditive $ mreplicate r (Additive a)

instance ((Additive-Monoid) a, (Additive-Group) a) => RightSemimodule Integer a where
  rscale r a = unAdditive $ greplicate r (Additive a)

instance RightSemimodule r a => RightSemimodule r (e -> a) where 
  rscale r = fmap (.* r)

instance RightSemimodule r a => RightSemimodule r (Op a e) where 
  rscale r (Op f) = Op $ fmap (.* r) f

instance (RightSemimodule r a, RightSemimodule r b) => RightSemimodule r (a, b) where
  rscale n (a, b) = (a .* n, b .* n)

instance (RightSemimodule r a, RightSemimodule r b, RightSemimodule r c) => RightSemimodule r (a, b, c) where
  rscale n (a, b, c) = (a .* n, b .* n, c .* n)

instance Semiring a => RightSemimodule a (Ratio a) where 
  rscale r (x :% y) = (r * x) :% y

--instance Ring a => RightSemimodule a (Complex a) where 
--  rscale r (x :+ y) = (r * x) :+ (r * y)

--instance Ring a => RightSemimodule (Complex a) (Complex a) where 
--  rscale = (*) 

#define deriveRightSemimodule(ty)                     \
instance RightSemimodule ty ty where {                \
   rscale = (*)                                       \
;  {-# INLINE rscale #-}                              \
}

deriveRightSemimodule(Bool)
deriveRightSemimodule(Int)
deriveRightSemimodule(Int8)
deriveRightSemimodule(Int16)
deriveRightSemimodule(Int32)
deriveRightSemimodule(Int64)
deriveRightSemimodule(Word)
deriveRightSemimodule(Word8)
deriveRightSemimodule(Word16)
deriveRightSemimodule(Word32)
deriveRightSemimodule(Word64)
deriveRightSemimodule(Uni)
deriveRightSemimodule(Deci)
deriveRightSemimodule(Centi)
deriveRightSemimodule(Milli)
deriveRightSemimodule(Micro)
deriveRightSemimodule(Nano)
deriveRightSemimodule(Pico)
deriveRightSemimodule(Float)
deriveRightSemimodule(Double)
deriveRightSemimodule(CFloat)
deriveRightSemimodule(CDouble)
deriveRightSemimodule((Ratio Integer))
deriveRightSemimodule((Ratio Natural))

instance Semiring r => Bisemimodule r r ()

instance Bisemimodule r r a => Bisemimodule r r (e -> a)

instance Bisemimodule r r a => Bisemimodule r r (Op a e)

instance (Bisemimodule r r a, Bisemimodule r r b) => Bisemimodule r r (a, b)

instance (Bisemimodule r r a, Bisemimodule r r b, Bisemimodule r r c) => Bisemimodule r r (a, b, c)

instance Semiring a => Bisemimodule a a (Ratio a)

--instance Ring a => Bisemimodule a a (Complex a)

--instance Ring a => Bisemimodule (Complex a) (Complex a) (Complex a)


#define deriveBisemimodule(ty)                     \
instance Bisemimodule ty ty ty                        \

deriveBisemimodule(Bool)
deriveBisemimodule(Int)
deriveBisemimodule(Int8)
deriveBisemimodule(Int16)
deriveBisemimodule(Int32)
deriveBisemimodule(Int64)
deriveBisemimodule(Word)
deriveBisemimodule(Word8)
deriveBisemimodule(Word16)
deriveBisemimodule(Word32)
deriveBisemimodule(Word64)
deriveBisemimodule(Uni)
deriveBisemimodule(Deci)
deriveBisemimodule(Centi)
deriveBisemimodule(Milli)
deriveBisemimodule(Micro)
deriveBisemimodule(Nano)
deriveBisemimodule(Pico)
deriveBisemimodule(Float)
deriveBisemimodule(Double)
deriveBisemimodule(CFloat)
deriveBisemimodule(CDouble)
deriveBisemimodule((Ratio Integer))
deriveBisemimodule((Ratio Natural))
