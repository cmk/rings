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
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE RankNTypes                 #-}

module Data.Semimodule.Matrix (
    type M22
  , type M23
  , type M24
  , type M32
  , type M33
  , type M34
  , type M42
  , type M43
  , type M44
  , lensRep
  , grateRep
  , tran
  , row
  , rows
  , col
  , cols
  , (.#)
  , (.*)
  , (#.)
  , (*.)
  , (.#.)
  , (.*.)
  , outer
  , scale
  , dirac
  , identity
  , transpose
  , trace
  , diagonal
  , bdet2
  , det2
  , inv2
  , bdet3
  , det3
  , inv3
  , bdet4
  , det4
  , inv4
  , m22
  , m23
  , m24
  , m32
  , m33
  , m34
  , m42
  , m43
  , m44
  ) where

import safe Data.Bool
import safe Data.Distributive
import safe Data.Functor.Compose
import safe Data.Functor.Rep
import safe Data.Semifield
import safe Data.Semigroup.Additive
import safe Data.Semigroup.Multiplicative
import safe Data.Semimodule
import safe Data.Semimodule.Transform
import safe Data.Semimodule.Vector
import safe Data.Semiring
import safe Data.Tuple
import safe Prelude hiding (Num(..), Fractional(..), sum, negate)


-- All matrices use row-major representation.

-- | A 2x2 matrix.
type M22 a = V2 (V2 a)

-- | A 2x3 matrix.
type M23 a = V2 (V3 a)

-- | A 2x4 matrix.
type M24 a = V2 (V4 a)

-- | A 3x2 matrix.
type M32 a = V3 (V2 a)

-- | A 3x3 matrix.
type M33 a = V3 (V3 a)

-- | A 3x4 matrix.
type M34 a = V3 (V4 a)

-- | A 4x2 matrix.
type M42 a = V4 (V2 a)

-- | A 4x3 matrix.
type M43 a = V4 (V3 a)

-- | A 4x4 matrix.
type M44 a = V4 (V4 a)

lensRep :: Eq (Rep f) => Representable f => Rep f -> forall g. Functor g => (a -> g a) -> f a -> g (f a)
lensRep i f s = setter s <$> f (getter s)
  where getter = flip index i
        setter s' b = tabulate $ \j -> bool (index s' j) b (i == j)
{-# INLINE lensRep #-}

grateRep :: Representable f => forall g. Functor g => (Rep f -> g a -> b) -> g (f a) -> f b
grateRep iab s = tabulate $ \i -> iab i (fmap (`index` i) s)
{-# INLINE grateRep #-}

-- @ ('.#') = 'app' . 'tran' @
tran :: Semiring a => Basis b f => Basis c g => Foldable g => f (g a) -> Tran a b c
tran m = Tran $ \f -> index $ m .# (tabulate f)

-- | Retrieve a row of a row-major matrix or element of a row vector.
--
-- >>> row I21 (V2 1 2)
-- 1
--
row :: Representable f => Rep f -> f a -> a
row = flip index
{-# INLINE row #-}

-- | Retrieve a column of a row-major matrix.
--
-- >>> row I22 . col I31 $ V2 (V3 1 2 3) (V3 4 5 6)
-- 4
--
col :: Functor f => Representable g => Rep g -> f (g a) -> f a
col j = flip index j . distribute
{-# INLINE col #-}

-- | Outer product of two vectors.
--
-- >>> V2 1 1 `outer` V2 1 1
-- V2 (V2 1 1) (V2 1 1)
--
outer :: Semiring a => Functor f => Functor g => f a -> g a -> f (g a)
outer x y = fmap (\z-> fmap (*z) y) x

infixl 7 #.

-- | Multiply a matrix on the left by a row vector.
--
-- >>> V2 1 2 #. m23 3 4 5 6 7 8
-- V3 15 18 21
--
-- >>> V2 1 2 #. m23 3 4 5 6 7 8 #. m32 1 0 0 0 0 0
-- V2 15 0
--
(#.) :: (Semiring a, Free f, Foldable f, Free g) => f a -> f (g a) -> g a
x #. y = tabulate (\j -> x .*. col j y)
{-# INLINE (#.) #-}

infixr 7 .#, .#.

-- | Multiply a matrix on the right by a column vector.
--
-- @ ('.#') = 'app' . 'fromMatrix' @
--
-- >>> m23 1 2 3 4 5 6 .# V3 7 8 9
-- V2 50 122
--
-- >>> m22 1 0 0 0 .# m23 1 2 3 4 5 6 .# V3 7 8 9
-- V2 50 0
--
(.#) :: (Semiring a, Free f, Free g, Foldable g) => f (g a) -> g a -> f a
x .# y = tabulate (\i -> row i x .*. y)
{-# INLINE (.#) #-}

-- | Multiply two matrices.
--
-- >>> m22 1 2 3 4 .#. m22 1 2 3 4 :: M22 Int
-- V2 (V2 7 10) (V2 15 22)
-- 
-- >>> m23 1 2 3 4 5 6 .#. m32 1 2 3 4 4 5 :: M22 Int
-- V2 (V2 19 25) (V2 43 58)
--
(.#.) :: (Semiring a, Free f, Free g, Free h, Foldable g) => f (g a) -> g (h a) -> f (h a)
(.#.) x y = getCompose $ tabulate (\(i,j) -> row i x .*. col j y)
{-# INLINE (.#.) #-}

-- | Obtain a diagonal matrix from a vector.
--
-- >>> scale (V2 2 3)
-- V2 (V2 2 0) (V2 0 3)
--
scale :: (Additive-Monoid) a => Free f => f a -> f (f a)
scale f = flip imapRep f $ \i x -> flip imapRep f (\j _ -> bool zero x $ i == j)
{-# INLINE scale #-}

-- | Identity matrix.
--
-- >>> identity :: M44 Int
-- V4 (V4 1 0 0 0) (V4 0 1 0 0) (V4 0 0 1 0) (V4 0 0 0 1)
--
-- >>> identity :: V3 (V3 Int)
-- V3 (V3 1 0 0) (V3 0 1 0) (V3 0 0 1)
--
identity :: Semiring a => Free f => f (f a)
identity = scale $ pureRep one
{-# INLINE identity #-}

-- | Compute the trace of a matrix.
--
-- >>> trace (V2 (V2 a b) (V2 c d))
-- a <> d
--
trace :: Semiring a => Free f => Foldable f => f (f a) -> a
trace = sum . diagonal
{-# INLINE trace #-}

-- | Obtain the diagonal of a matrix as a vector.
--
-- >>> diagonal (V2 (V2 a b) (V2 c d))
-- V2 a d
--
diagonal :: Representable f => f (f a) -> f a
diagonal = flip bindRep id
{-# INLINE diagonal #-}

ij :: Representable f => Representable g => Rep f -> Rep g -> f (g a) -> a
ij i j = row i . col j

-- | 2x2 matrix bdeterminant over a commutative semiring.
--
-- >>> bdet2 $ m22 1 2 3 4
-- (4,6)
--
bdet2 :: Semiring a => Basis I2 f => Basis I2 g => f (g a) -> (a, a)
bdet2 m = (ij I21 I21 m * ij I22 I22 m, ij I21 I22 m * ij I22 I21 m)
{-# INLINE bdet2 #-}

-- | 2x2 matrix determinant over a commutative ring.
--
-- @
-- 'det2' '==' 'uncurry' ('-') . 'bdet2'
-- @
--
-- >>> det2 $ m22 1 2 3 4 :: Double
-- -2.0
--
det2 :: Ring a => Basis I2 f => Basis I2 g => f (g a) -> a
det2 = uncurry (-) . bdet2 
{-# INLINE det2 #-}

-- | 2x2 matrix inverse over a field.
--
-- >>> inv2 $ m22 1 2 3 4 :: M22 Double
-- V2 (V2 (-2.0) 1.0) (V2 1.5 (-0.5))
--
inv2 :: Field a => Basis I2 f => Basis I2 g => f (g a) -> g (f a) 
inv2 m = multl (recip $ det2 m) <$> m22 d (-b) (-c) a where
  a = ij I21 I21 m
  b = ij I21 I22 m
  c = ij I22 I21 m
  d = ij I22 I22 m
{-# INLINE inv2 #-}

-- | 3x3 matrix bdeterminant over a commutative semiring.
--
-- >>> bdet3 (V3 (V3 1 2 3) (V3 4 5 6) (V3 7 8 9))
-- (225, 225)
--
bdet3 :: Semiring a => Basis I3 f => Basis I3 g => f (g a) -> (a, a)
bdet3 m = (evens, odds) where
  evens = a*e*i + g*b*f + d*h*c
  odds  = a*h*f + d*b*i + g*e*c
  a = ij I31 I31 m
  b = ij I31 I32 m
  c = ij I31 I33 m
  d = ij I32 I31 m
  e = ij I32 I32 m
  f = ij I32 I33 m
  g = ij I33 I31 m
  h = ij I33 I32 m
  i = ij I33 I33 m
{-# INLINE bdet3 #-}

-- | 3x3 double-precision matrix determinant.
--
-- @
-- 'det3' '==' 'uncurry' ('-') . 'bdet3'
-- @
--
-- Implementation uses a cofactor expansion to avoid loss of precision.
--
-- >>> det3 (V3 (V3 1 2 3) (V3 4 5 6) (V3 7 8 9))
-- 0
--
det3 :: Ring a => Basis I3 f => Basis I3 g => f (g a) -> a
det3 m = a * (e*i-f*h) - d * (b*i-c*h) + g * (b*f-c*e) where
  a = ij I31 I31 m
  b = ij I31 I32 m
  c = ij I31 I33 m
  d = ij I32 I31 m
  e = ij I32 I32 m
  f = ij I32 I33 m
  g = ij I33 I31 m
  h = ij I33 I32 m
  i = ij I33 I33 m
{-# INLINE det3 #-}

-- | 3x3 matrix inverse.
--
-- >>> inv3 $ m33 1 2 4 4 2 2 1 1 1 :: M33 Double
-- V3 (V3 0.0 0.5 (-1.0)) (V3 (-0.5) (-0.75) 3.5) (V3 0.5 0.25 (-1.5))
--
inv3 :: forall a f g. Field a => Basis I3 f => Basis I3 g => f (g a) -> g (f a)
inv3 m = multl (recip $ det3 m) <$> m33 a' b' c' d' e' f' g' h' i' where
  a = ij I31 I31 m
  b = ij I31 I32 m
  c = ij I31 I33 m
  d = ij I32 I31 m
  e = ij I32 I32 m
  f = ij I32 I33 m
  g = ij I33 I31 m
  h = ij I33 I32 m
  i = ij I33 I33 m
  a' = cofactor (e,f,h,i)
  b' = cofactor (c,b,i,h)
  c' = cofactor (b,c,e,f)
  d' = cofactor (f,d,i,g)
  e' = cofactor (a,c,g,i)
  f' = cofactor (c,a,f,d)
  g' = cofactor (d,e,g,h)
  h' = cofactor (b,a,h,g)
  i' = cofactor (a,b,d,e)
  cofactor (q,r,s,t) = det2 (m22 q r s t :: M22 a)
{-# INLINE inv3 #-}

-- | 4x4 matrix bdeterminant over a commutative semiring.
--
-- >>> bdet4 (V4 (V4 1 2 3 4) (V4 5 6 7 8) (V4 9 10 11 12) (V4 13 14 15 16))
-- (27728,27728)
--
bdet4 :: Semiring a => Basis I4 f => Basis I4 g => f (g a) -> (a, a) 
bdet4 x = (evens, odds) where
  evens = a * (f*k*p + g*l*n + h*j*o) +
          b * (g*i*p + e*l*o + h*k*m) +
          c * (e*j*p + f*l*m + h*i*n) +
          d * (f*i*o + e*k*n + g*j*m)
  odds =  a * (g*j*p + f*l*o + h*k*n) +
          b * (e*k*p + g*l*m + h*i*o) +
          c * (f*i*p + e*l*n + h*j*m) +
          d * (e*j*o + f*k*m + g*i*n)
  a = ij I41 I41 x
  b = ij I41 I42 x
  c = ij I41 I43 x
  d = ij I41 I44 x
  e = ij I42 I41 x
  f = ij I42 I42 x
  g = ij I42 I43 x
  h = ij I42 I44 x
  i = ij I43 I41 x
  j = ij I43 I42 x
  k = ij I43 I43 x
  l = ij I43 I44 x
  m = ij I44 I41 x
  n = ij I44 I42 x
  o = ij I44 I43 x
  p = ij I44 I44 x
{-# INLINE bdet4 #-}

-- | 4x4 matrix determinant over a commutative ring.
--
-- @
-- 'det4' '==' 'uncurry' ('-') . 'bdet4'
-- @
--
-- This implementation uses a cofactor expansion to avoid loss of precision.
--
-- >>> det4 (m44 1 0 3 2 2 0 2 1 0 0 0 1 0 3 4 0 :: M44 Rational)
-- (-12) % 1
--
det4 :: Ring a => Basis I4 f => Basis I4 g => f (g a) -> a
det4 x = s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0 where
  s0 = i00 * i11 - i10 * i01
  s1 = i00 * i12 - i10 * i02
  s2 = i00 * i13 - i10 * i03
  s3 = i01 * i12 - i11 * i02
  s4 = i01 * i13 - i11 * i03
  s5 = i02 * i13 - i12 * i03

  c5 = i22 * i33 - i32 * i23
  c4 = i21 * i33 - i31 * i23
  c3 = i21 * i32 - i31 * i22
  c2 = i20 * i33 - i30 * i23
  c1 = i20 * i32 - i30 * i22
  c0 = i20 * i31 - i30 * i21

  i00 = ij I41 I41 x
  i01 = ij I41 I42 x
  i02 = ij I41 I43 x
  i03 = ij I41 I44 x
  i10 = ij I42 I41 x
  i11 = ij I42 I42 x
  i12 = ij I42 I43 x
  i13 = ij I42 I44 x
  i20 = ij I43 I41 x
  i21 = ij I43 I42 x
  i22 = ij I43 I43 x
  i23 = ij I43 I44 x
  i30 = ij I44 I41 x
  i31 = ij I44 I42 x
  i32 = ij I44 I43 x
  i33 = ij I44 I44 x
{-# INLINE det4 #-}

-- | 4x4 matrix inverse.
--
-- >>> row I41 $ inv4 (m44 1 0 3 2 2 0 2 1 0 0 0 1 0 3 4 0 :: M44 Rational)
-- V4 (6 % (-12)) ((-9) % (-12)) ((-3) % (-12)) (0 % (-12))
--
inv4 :: forall a f g. Field a => Basis I4 f => Basis I4 g => f (g a) -> g (f a)
inv4 x =  multl (recip det) <$> x' where
  i00 = ij I41 I41 x
  i01 = ij I41 I42 x
  i02 = ij I41 I43 x
  i03 = ij I41 I44 x
  i10 = ij I42 I41 x
  i11 = ij I42 I42 x
  i12 = ij I42 I43 x
  i13 = ij I42 I44 x
  i20 = ij I43 I41 x
  i21 = ij I43 I42 x
  i22 = ij I43 I43 x
  i23 = ij I43 I44 x
  i30 = ij I44 I41 x
  i31 = ij I44 I42 x
  i32 = ij I44 I43 x
  i33 = ij I44 I44 x

  s0 = i00 * i11 - i10 * i01
  s1 = i00 * i12 - i10 * i02
  s2 = i00 * i13 - i10 * i03
  s3 = i01 * i12 - i11 * i02
  s4 = i01 * i13 - i11 * i03
  s5 = i02 * i13 - i12 * i03
  c5 = i22 * i33 - i32 * i23
  c4 = i21 * i33 - i31 * i23
  c3 = i21 * i32 - i31 * i22
  c2 = i20 * i33 - i30 * i23
  c1 = i20 * i32 - i30 * i22
  c0 = i20 * i31 - i30 * i21

  det = s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0

  x' = m44 (i11 * c5 - i12 * c4 + i13 * c3)
           (-i01 * c5 + i02 * c4 - i03 * c3)
           (i31 * s5 - i32 * s4 + i33 * s3)
           (-i21 * s5 + i22 * s4 - i23 * s3)
           (-i10 * c5 + i12 * c2 - i13 * c1)
           (i00 * c5 - i02 * c2 + i03 * c1)
           (-i30 * s5 + i32 * s2 - i33 * s1)
           (i20 * s5 - i22 * s2 + i23 * s1)
           (i10 * c4 - i11 * c2 + i13 * c0)
           (-i00 * c4 + i01 * c2 - i03 * c0)
           (i30 * s4 - i31 * s2 + i33 * s0)
           (-i20 * s4 + i21 * s2 - i23 * s0)
           (-i10 * c3 + i11 * c1 - i12 * c0)
           (i00 * c3 - i01 * c1 + i02 * c0)
           (-i30 * s3 + i31 * s1 - i32 * s0)
           (i20 * s3 - i21 * s1 + i22 * s0)
{-# INLINE inv4 #-}

-- | Construct a 2x2 matrix.
--
-- Arguments are in row-major order.
--
-- >>> m22 1 2 3 4 :: M22 Int
-- V2 (V2 1 2) (V2 3 4)
--
-- @ 'm22' :: a -> a -> a -> a -> 'M22' a @
--
m22 :: Basis I2 f => Basis I2 g => a -> a -> a -> a -> f (g a)
m22 a b c d = fillI2 (fillI2 a b) (fillI2 c d)
{-# INLINE m22 #-}

-- | Construct a 2x3 matrix.
--
-- Arguments are in row-major order.
--
-- @ 'm23' :: a -> a -> a -> a -> a -> a -> 'M23' a @
--
m23 :: Basis I2 f => Basis I3 g => a -> a -> a -> a -> a -> a -> f (g a)
m23 a b c d e f = fillI2 (fillI3 a b c) (fillI3 d e f)
{-# INLINE m23 #-}

-- | Construct a 2x4 matrix.
--
-- Arguments are in row-major order.
--
m24 :: Basis I2 f => Basis I4 g => a -> a -> a -> a -> a -> a -> a -> a -> f (g a)
m24 a b c d e f g h = fillI2 (fillI4 a b c d) (fillI4 e f g h)
{-# INLINE m24 #-}

-- | Construct a 3x2 matrix.
--
-- Arguments are in row-major order.
--
m32 :: Basis I3 f => Basis I2 g => a -> a -> a -> a -> a -> a -> f (g a)
m32 a b c d e f = fillI3 (fillI2 a b) (fillI2 c d) (fillI2 e f)
{-# INLINE m32 #-}

-- | Construct a 3x3 matrix.
--
-- Arguments are in row-major order.
--
m33 :: Basis I3 f => Basis I3 g => a -> a -> a -> a -> a -> a -> a -> a -> a -> f (g a)
m33 a b c d e f g h i = fillI3 (fillI3 a b c) (fillI3 d e f) (fillI3 g h i)
{-# INLINE m33 #-}

-- | Construct a 3x4 matrix.
--
-- Arguments are in row-major order.
--
m34 :: Basis I3 f => Basis I4 g => a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> f (g a)
m34 a b c d e f g h i j k l = fillI3 (fillI4 a b c d) (fillI4 e f g h) (fillI4 i j k l)
{-# INLINE m34 #-}

-- | Construct a 4x2 matrix.
--
-- Arguments are in row-major order.
--
m42 :: Basis I4 f => Basis I2 g => a -> a -> a -> a -> a -> a -> a -> a -> f (g a)
m42 a b c d e f g h = fillI4 (fillI2 a b) (fillI2 c d) (fillI2 e f) (fillI2 g h)
{-# INLINE m42 #-}

-- | Construct a 4x3 matrix.
--
-- Arguments are in row-major order.
--
m43 :: Basis I4 f => Basis I3 g => a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> f (g a)
m43 a b c d e f g h i j k l = fillI4 (fillI3 a b c) (fillI3 d e f) (fillI3 g h i) (fillI3 j k l)
{-# INLINE m43 #-}

-- | Construct a 4x4 matrix.
--
-- Arguments are in row-major order.
--
m44 :: Basis I4 f => Basis I4 g => a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> f (g a)
m44 a b c d e f g h i j k l m n o p = fillI4 (fillI4 a b c d) (fillI4 e f g h) (fillI4 i j k l) (fillI4 m n o p)
{-# INLINE m44 #-}
