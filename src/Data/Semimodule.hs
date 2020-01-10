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

module Data.Semimodule where

import safe Data.Bool
import safe Data.Complex
import safe Data.Semifield
import safe Data.Fixed
import safe Data.Functor.Compose
import safe Data.Functor.Rep
import safe Data.Group
import safe Data.Int
import safe Data.Semiring
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Tuple
import safe Data.Word
import safe GHC.Real hiding (Fractional(..))
import safe Numeric.Natural
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe Prelude hiding (Num(..), Fractional(..), sum, product)
import safe qualified Prelude as N

import safe Data.Semigroup.Additive as A
import safe Data.Semigroup.Multiplicative as M

import safe Data.Magma

type Free f = (Foldable1 f, Representable f, Eq (Rep f))

{-
type Module r a = (Ring r, Group a, Semimodule r a)

-- Module over a field
-- classical vector spaces
type VSpace r a = (Field r, Module r a)

-- Semimodule over a semifield
-- dioids
type DSpace r a = (Semifield r, Semimodule r a)


-- | Free semimodule over a generating set.
--
type FreeSemimodule a f = (Free f, Semimodule a (f a))

type FreeModule a f = (Free f, Module a (f a))

type CommutativeGroup a = Module Integer a

-}


--instance (Unital (f a), Algebra (f a), Functor f) => Semifield (f a) where
  --recip q = conj' q // norm' q
--  recip q = ((recip . norm' $ q) ><) <$> conj' q 

type Module r a = (Ring r, Group a, Semimodule r a)

infixl 7 .*, *.

-- | < https://en.wikipedia.org/wiki/Semimodule Semimodule > over a commutative semiring.
--
-- All instances must satisfy the following identities:
-- 
-- @ r '*.' (x '<>' y) ≡ r '*.' x '<>' r '*.' y @
--
-- @ (r '+' s) '*.' x ≡ r '*.' x '<>' s '*.' x @
--
-- @ (r '*' s) '*.' x ≡ r '*.' (s '*.' x) @
--
-- When the ring of coefficients /r/ is unital we must additionally have:
--
-- @ 'one' '*.' x ≡ x @
--
-- See the properties module for a detailed specification of the laws.
--
class (Semiring r, Semigroup a) => Semimodule r a where

  -- | Left-multiply by a scalar.
  --
  (*.) :: r -> a -> a
  (*.) = flip (.*)
  
  -- | Right-multiply by a scalar.
  --
  (.*) :: a -> r -> a
  (.*) = flip (*.)

-- | Default definition of 'negate' for a commutative group.
--
--negateDef :: CommutativeGroup a => a -> a
--negateDef a = (-1 :: Integer) *. a

-- | Default definition of '(*.)' for a free module.
--
lmultRep :: Semiring a => Functor f => a -> f a -> f a
lmultRep a f = (a *) <$> f

-- | Default definition of '(.*)' for a free module.
--
rmultRep :: Semiring a => Functor f => f a -> a -> f a
rmultRep f a = (* a) <$> f

{-

u = V3 (1 :% 1) (2 :% 1) (3 :% 1) :: V3 Rational
v = V3 (2 :% 1) (4 :% 1) (6 :% 1) :: V3 Rational
r = 1 :% 2 :: Rational
lerp r u v
-- V3 (6 % 4) (12 % 4) (18 % 4)

u = V3 (1 :% 1) (2 :% 1) (3 :% 1) :: V3 Positive
v = V3 (2 :% 1) (4 :% 1) (6 :% 1) :: V3 Positive
r = 1 :% 2 :: Positive
lerp r u v

-}
-- | Linearly interpolate between two vectors.
--
lerp :: Module r a => r -> a -> a -> a
lerp r f g = r *. f <> (one - r) *. g
{-# INLINE lerp #-}

infix 6 .*.

-- | Dot product.
--
(.*.) :: Free f => Presemiring a => f a -> f a -> a
(.*.) a b = sum1 $ liftR2 (*) a b -- mzipWithRep (*) a b
{-# INLINE (.*.) #-}

-- | Squared /l2/ norm of a vector.
--
quadrance :: Free f => Presemiring a => f a -> a
quadrance f = f .*. f
{-# INLINE quadrance #-}

-- | Squared /l2/ norm of the difference between two vectors.
--
qd :: Free f => Module a (f a) => f a -> f a -> a
qd f g = quadrance $ f << g
{-# INLINE qd #-}

-- | Dirac delta function.
--
dirac :: Eq i => Semiring a => i -> i -> a
dirac i j = bool zero one (i == j)
{-# INLINE dirac #-}

-- | Create a unit vector at an index.
--
-- >>> idx I21 :: V2 Int
-- V2 1 0
--
-- >>> idx I42 :: V4 Int
-- V4 0 1 0 0
--
idx :: Free f => Semiring a => Rep f -> f a
idx i = tabulate $ dirac i
{-# INLINE idx #-}

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semiring r => Semimodule r () where 
  _ *. _ = ()

instance Semigroup a => Semimodule () a where 
  _ *. a = a

instance Monoid a => Semimodule Natural a where
  (*.) = mreplicate

instance Group a => Semimodule Integer a where
  (*.) = greplicate

instance Semimodule r a => Semimodule r (e -> a) where 
  a *. f = (a *.) <$> f

instance (Semimodule r a, Semimodule r b) => Semimodule r (a, b) where
  n *. (a, b) = (n *. a, n *. b)

instance (Semimodule r a, Semimodule r b, Semimodule r c) => Semimodule r (a, b, c) where
  n *. (a, b, c) = (n *. a, n *. b, n *. c)

instance (Semiring a, Semimodule r a) => Semimodule r (Additive (Ratio a)) where 
  a *. (Additive (x :% y)) = Additive $ (a *. x) :% y

instance (Ring a, Semimodule r a) => Semimodule r (Additive (Complex a)) where 
  a *. (Additive (x :+ y)) = Additive $ (a *. x) :+ (a *. y)

#define deriveSemimodule(ty)                                 \
instance Semiring ty => Semimodule ty (Additive ty) where {  \
   r *. (Additive a) = Additive $ r * a                                \
;  {-# INLINE (*.) #-}                                       \
}

deriveSemimodule(Bool)
deriveSemimodule(Int)
deriveSemimodule(Int8)
deriveSemimodule(Int16)
deriveSemimodule(Int32)
deriveSemimodule(Int64)
deriveSemimodule(Word)
deriveSemimodule(Word8)
deriveSemimodule(Word16)
deriveSemimodule(Word32)
deriveSemimodule(Word64)
deriveSemimodule(Uni)
deriveSemimodule(Deci)
deriveSemimodule(Centi)
deriveSemimodule(Milli)
deriveSemimodule(Micro)
deriveSemimodule(Nano)
deriveSemimodule(Pico)
deriveSemimodule(Float)
deriveSemimodule(Double)
deriveSemimodule(CFloat)
deriveSemimodule(CDouble)
