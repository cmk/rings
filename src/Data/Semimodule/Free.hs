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
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE RankNTypes               #-}

module Data.Semimodule.Free (
  -- * Vector types
    V1(..)
  , unV1
  , V2(..)
  , V3(..)
  , cross
  , triple
  , V4(..)
  -- * Matrix types
  , type M11
  , type M12
  , type M13
  , type M14
  , type M21
  , type M31
  , type M41
  , type M22
  , type M23
  , type M24
  , type M32
  , type M33
  , type M34
  , type M42
  , type M43
  , type M44
  , m11
  , m12
  , m13
  , m14
  , m21
  , m31
  , m41
  , m22
  , m23
  , m24
  , m32
  , m33
  , m34
  , m42
  , m43
  , m44
  -- * Matrix determinants & inverses
  , inv1
  , inv2
  , bdet2
  , det2
  , bdet3
  , det3
  , inv3
  , bdet4
  , det4
  , inv4
) where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Distributive
import safe Data.Functor.Classes
import safe Data.Functor.Compose
import safe Data.Functor.Rep hiding (Co)
import safe Data.Semifield
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Semimodule
import safe Data.Semimodule.Basis
import safe Data.Semimodule.Operator
import safe Data.Semiring
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import safe Prelude (fromInteger)


-------------------------------------------------------------------------------
-- Vectors
-------------------------------------------------------------------------------

unV1 :: V1 a -> a
unV1 (V1 a) = a

newtype V1 a = V1 a deriving (Eq,Ord,Show)

data V2 a = V2 !a !a deriving (Eq,Ord,Show)

data V3 a = V3 !a !a !a deriving (Eq,Ord,Show)

data V4 a = V4 !a !a !a !a deriving (Eq,Ord,Show)

-- | Cross product.
--
-- @ 
-- a `'cross'` a = 'zero'
-- a `'cross'` b = 'negate' ( b `'cross'` a ) , 
-- a `'cross'` ( b '+' c ) = ( a `'cross'` b ) '+' ( a `'cross'` c ) , 
-- ( r a ) `'cross'` b = a `'cross'` ( r b ) = r ( a `'cross'` b ) . 
-- a `'cross'` ( b `'cross'` c ) '+' b `'cross'` ( c `'cross'` a ) '+' c `'cross'` ( a `'cross'` b ) = 'zero' . 
-- @
--
-- See < https://en.wikipedia.org/wiki/Jacobi_identity Jacobi identity >.
--
cross :: Ring a => V3 a -> V3 a -> V3 a
cross (V3 a b c) (V3 d e f) = V3 (b*f-c*e) (c*d-a*f) (a*e-b*d)
{-# INLINABLE cross #-}

-- | Scalar triple product.
--
-- @
-- 'triple' x y z = 'triple' z x y = 'triple' y z x
-- 'triple' x y z = 'negate' '$' 'triple' x z y = 'negate' '$' 'triple' y x z
-- 'triple' x x y = 'triple' x y y = 'triple' x y x = 'zero'
-- ('triple' x y z) '*.' x = (x `'cross'` y) `'cross'` (x `'cross'` z)
-- @
--
-- >>> triple (V3 0 0 1) (V3 1 0 0) (V3 0 1 0) :: Double
-- 1.0
--
triple :: Ring a => V3 a -> V3 a -> V3 a -> a
triple x y z = inner x (cross y z)
{-# INLINE triple #-}


-------------------------------------------------------------------------------
-- Matrices
-------------------------------------------------------------------------------

-- All matrices use row-major representation.

-- | A 1x1 matrix.
type M11 = Compose V1 V1

-- | A 1x2 matrix.
type M12 = Compose V1 V2

-- | A 1x3 matrix.
type M13 = Compose V1 V3

-- | A 1x4 matrix.
type M14 = Compose V1 V4

-- | A 2x1 matrix.
type M21 = Compose V2 V1

-- | A 3x1 matrix.
type M31 = Compose V3 V1

-- | A 4x1 matrix.
type M41 = Compose V4 V1

-- | A 2x2 matrix.
type M22 = Compose V2 V2

-- | A 2x3 matrix.
type M23 = Compose V2 V3

-- | A 2x4 matrix.
type M24 = Compose V2 V4

-- | A 3x2 matrix.
type M32 = Compose V3 V2

-- | A 3x3 matrix.
type M33 = Compose V3 V3

-- | A 3x4 matrix.
type M34 = Compose V3 V4

-- | A 4x2 matrix.
type M42 = Compose V4 V2

-- | A 4x3 matrix.
type M43 = Compose V4 V3

-- | A 4x4 matrix.
type M44 = Compose V4 V4

-------------------------------------------------------------------------------
-- Matrix constructors
-------------------------------------------------------------------------------

-- | Construct a 1x1 matrix.
--
-- >>> m11 1 :: M11 Int
-- Compose (V1 (V1 1))
--
m11 :: a -> M11 a
m11 a = Compose $ V1 (V1 a)
{-# INLINE m11 #-}

-- | Construct a 1x2 matrix.
--
-- >>> m12 1 2 :: M12 Int
-- Compose (V1 (V2 1 2))
--
m12 :: a -> a -> M12 a
m12 a b = Compose $ V1 (V2 a b)
{-# INLINE m12 #-}

-- | Construct a 1x3 matrix.
--
-- >>> m13 1 2 3 :: M13 Int
-- Compose (V1 (V3 1 2 3))
--
m13 :: a -> a -> a -> M13 a
m13 a b c = Compose $ V1 (V3 a b c)
{-# INLINE m13 #-}

-- | Construct a 1x4 matrix.
--
-- >>> m14 1 2 3 4 :: M14 Int
-- Compose (V1 (V4 1 2 3 4))
--
m14 :: a -> a -> a -> a -> M14 a
m14 a b c d = Compose $ V1 (V4 a b c d)
{-# INLINE m14 #-}

-- | Construct a 2x1 matrix.
--
-- >>> m21 1 2 :: M21 Int
-- Compose (V2 (V1 1) (V1 2))
--
m21 :: a -> a -> M21 a
m21 a b = Compose $ V2 (V1 a) (V1 b)
{-# INLINE m21 #-}

-- | Construct a 3x1 matrix.
--
-- >>> m31 1 2 3 :: M31 Int
-- Compose (V3 (V1 1) (V1 2) (V1 3))
--
m31 :: a -> a -> a -> M31 a
m31 a b c = Compose $ V3 (V1 a) (V1 b) (V1 c)
{-# INLINE m31 #-}

-- | Construct a 4x1 matrix.
--
-- >>> m41 1 2 3 4 :: M41 Int
-- Compose (V4 (V1 1) (V1 2) (V1 3) (V1 4))
--
m41 :: a -> a -> a -> a -> M41 a
m41 a b c d = Compose $ V4 (V1 a) (V1 b) (V1 c) (V1 d)
{-# INLINE m41 #-}

-- | Construct a 2x2 matrix.
--
-- Arguments are in row-major order.
--
-- >>> m22 1 2 3 4 :: M22 Int
-- Compose (V2 (V2 1 2) (V2 3 4))
--
m22 :: a -> a -> a -> a -> M22 a
m22 a b c d = Compose $ V2 (V2 a b) (V2 c d)
{-# INLINE m22 #-}

-- | Construct a 2x3 matrix.
--
-- Arguments are in row-major order.
--
m23 :: a -> a -> a -> a -> a -> a -> M23 a
m23 a b c d e f = Compose $ V2 (V3 a b c) (V3 d e f)
{-# INLINE m23 #-}

-- | Construct a 2x4 matrix.
--
-- Arguments are in row-major order.
--
m24 :: a -> a -> a -> a -> a -> a -> a -> a -> M24 a
m24 a b c d e f g h = Compose $ V2 (V4 a b c d) (V4 e f g h)
{-# INLINE m24 #-}

-- | Construct a 3x2 matrix.
--
-- Arguments are in row-major order.
--
m32 :: a -> a -> a -> a -> a -> a -> M32 a
m32 a b c d e f = Compose $ V3 (V2 a b) (V2 c d) (V2 e f)
{-# INLINE m32 #-}

-- | Construct a 3x3 matrix.
--
-- Arguments are in row-major order.
--
m33 :: a -> a -> a -> a -> a -> a -> a -> a -> a -> M33 a
m33 a b c d e f g h i = Compose $ V3 (V3 a b c) (V3 d e f) (V3 g h i)
{-# INLINE m33 #-}

-- | Construct a 3x4 matrix.
--
-- Arguments are in row-major order.
--
m34 :: a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> M34 a
m34 a b c d e f g h i j k l = Compose $ V3 (V4 a b c d) (V4 e f g h) (V4 i j k l)
{-# INLINE m34 #-}

-- | Construct a 4x2 matrix.
--
-- Arguments are in row-major order.
--
m42 :: a -> a -> a -> a -> a -> a -> a -> a -> M42 a
m42 a b c d e f g h = Compose $ V4 (V2 a b) (V2 c d) (V2 e f) (V2 g h)
{-# INLINE m42 #-}

-- | Construct a 4x3 matrix.
--
-- Arguments are in row-major order.
--
m43 :: a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> M43 a
m43 a b c d e f g h i j k l = Compose $ V4 (V3 a b c) (V3 d e f) (V3 g h i) (V3 j k l)
{-# INLINE m43 #-}

-- | Construct a 4x4 matrix.
--
-- Arguments are in row-major order.
--
m44 :: a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> M44 a
m44 a b c d e f g h i j k l m n o p = Compose $ V4 (V4 a b c d) (V4 e f g h) (V4 i j k l) (V4 m n o p)
{-# INLINE m44 #-}

-------------------------------------------------------------------------------
-- Matrix determinants and inverses
-------------------------------------------------------------------------------

-- | 1x1 matrix inverse over a field.
--
-- >>> inv1 $ m11 4.0 :: M11 Double
-- Compose (V1 (V1 0.25))
--
inv1 :: Field a => M11 a -> M11 a
inv1 = transpose . fmap recip

-- | 2x2 matrix bdeterminant over a commutative semiring.
--
-- >>> bdet2 $ m22 1 2 3 4
-- (4,6)
--
bdet2 :: Semiring a => Basis2 E2 E2 f g => (f**g) a -> (a, a)
bdet2 m = (elt2 E21 E21 m * elt2 E22 E22 m, elt2 E21 E22 m * elt2 E22 E21 m)
{-# INLINE bdet2 #-}

-- | 2x2 matrix determinant over a commutative ring.
--
-- @
-- 'det2' = 'uncurry' ('-') . 'bdet2'
-- @
--
-- >>> det2 $ m22 1 2 3 4 :: Double
-- -2.0
--
det2 :: Ring a => Basis2 E2 E2 f g => (f**g) a -> a
det2 = uncurry (-) . bdet2 
{-# INLINE det2 #-}

-- | 2x2 matrix inverse over a field.
--
-- >>> inv2 $ m22 1 2 3 4 :: M22 Double
-- Compose (V2 (V2 (-2.0) 1.0) (V2 1.5 (-0.5)))
--
inv2 :: Field a => M22 a -> M22 a
inv2 m = lscaleDef (recip $ det2 m) $ m22 d (-b) (-c) a where
  a = elt2 E21 E21 m
  b = elt2 E21 E22 m
  c = elt2 E22 E21 m
  d = elt2 E22 E22 m
{-# INLINE inv2 #-}

-- | 3x3 matrix bdeterminant over a commutative semiring.
--
-- >>> bdet3 (V3 (V3 1 2 3) (V3 4 5 6) (V3 7 8 9))
-- (225, 225)
--
bdet3 :: Semiring a => Basis2 E3 E3 f g => (f**g) a -> (a, a)
bdet3 m = (evens, odds) where
  evens = a*e*i + g*b*f + d*h*c
  odds  = a*h*f + d*b*i + g*e*c
  a = elt2 E31 E31 m
  b = elt2 E31 E32 m
  c = elt2 E31 E33 m
  d = elt2 E32 E31 m
  e = elt2 E32 E32 m
  f = elt2 E32 E33 m
  g = elt2 E33 E31 m
  h = elt2 E33 E32 m
  i = elt2 E33 E33 m
{-# INLINE bdet3 #-}

-- | 3x3 double-precision matrix determinant.
--
-- @
-- 'det3' = 'uncurry' ('-') . 'bdet3'
-- @
--
-- Implementation uses a cofactor expansion to avoid loss of precision.
--
-- >>> det3 $ m33 1 2 3 4 5 6 7 8 9
-- 0
--
det3 :: Ring a => Basis2 E3 E3 f g => (f**g) a -> a
det3 m = a * (e*i-f*h) - d * (b*i-c*h) + g * (b*f-c*e) where
  a = elt2 E31 E31 m
  b = elt2 E31 E32 m
  c = elt2 E31 E33 m
  d = elt2 E32 E31 m
  e = elt2 E32 E32 m
  f = elt2 E32 E33 m
  g = elt2 E33 E31 m
  h = elt2 E33 E32 m
  i = elt2 E33 E33 m
{-# INLINE det3 #-}

-- | 3x3 matrix inverse.
--
-- >>> inv3 $ m33 1 2 4 4 2 2 1 1 1 :: M33 Double
-- Compose (V3 (V3 0.0 0.5 (-1.0)) (V3 (-0.5) (-0.75) 3.5) (V3 0.5 0.25 (-1.5)))
--
inv3 :: Field a => M33 a -> M33 a
inv3 m = lscaleDef (recip $ det3 m) $ m33 a' b' c' d' e' f' g' h' i' where
  a = elt2 E31 E31 m
  b = elt2 E31 E32 m
  c = elt2 E31 E33 m
  d = elt2 E32 E31 m
  e = elt2 E32 E32 m
  f = elt2 E32 E33 m
  g = elt2 E33 E31 m
  h = elt2 E33 E32 m
  i = elt2 E33 E33 m
  a' = cofactor (e,f,h,i)
  b' = cofactor (c,b,i,h)
  c' = cofactor (b,c,e,f)
  d' = cofactor (f,d,i,g)
  e' = cofactor (a,c,g,i)
  f' = cofactor (c,a,f,d)
  g' = cofactor (d,e,g,h)
  h' = cofactor (b,a,h,g)
  i' = cofactor (a,b,d,e)
  cofactor (q,r,s,t) = det2 (m22 q r s t)
{-# INLINE inv3 #-}

-- | 4x4 matrix bdeterminant over a commutative semiring.
--
-- >>> bdet4 $ m44 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
-- (27728,27728)
--
bdet4 :: Semiring a => Basis2 E4 E4 f g => (f**g) a -> (a, a) 
bdet4 x = (evens, odds) where
  evens = a * (f*k*p + g*l*n + h*j*o) +
          b * (g*i*p + e*l*o + h*k*m) +
          c * (e*j*p + f*l*m + h*i*n) +
          d * (f*i*o + e*k*n + g*j*m)
  odds =  a * (g*j*p + f*l*o + h*k*n) +
          b * (e*k*p + g*l*m + h*i*o) +
          c * (f*i*p + e*l*n + h*j*m) +
          d * (e*j*o + f*k*m + g*i*n)
  a = elt2 E41 E41 x
  b = elt2 E41 E42 x
  c = elt2 E41 E43 x
  d = elt2 E41 E44 x
  e = elt2 E42 E41 x
  f = elt2 E42 E42 x
  g = elt2 E42 E43 x
  h = elt2 E42 E44 x
  i = elt2 E43 E41 x
  j = elt2 E43 E42 x
  k = elt2 E43 E43 x
  l = elt2 E43 E44 x
  m = elt2 E44 E41 x
  n = elt2 E44 E42 x
  o = elt2 E44 E43 x
  p = elt2 E44 E44 x
{-# INLINE bdet4 #-}

-- | 4x4 matrix determinant over a commutative ring.
--
-- @
-- 'det4' = 'uncurry' ('-') . 'bdet4'
-- @
--
-- This implementation uses a cofactor expansion to avoid loss of precision.
--
-- >>> det4 $ m44 1 0 3 2 2 0 2 1 0 0 0 1 0 3 4 0 :: Rational
-- (-12) % 1
--
det4 :: Ring a => Basis2 E4 E4 f g => (f**g) a -> a
det4 x = s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0 where
  s0 = i00 * e11 - e10 * i01
  s1 = i00 * e12 - e10 * i02
  s2 = i00 * e13 - e10 * i03
  s3 = i01 * e12 - e11 * i02
  s4 = i01 * e13 - e11 * i03
  s5 = i02 * e13 - e12 * i03

  c5 = e22 * e33 - e32 * e23
  c4 = e21 * e33 - e31 * e23
  c3 = e21 * e32 - e31 * e22
  c2 = e20 * e33 - e30 * e23
  c1 = e20 * e32 - e30 * e22
  c0 = e20 * e31 - e30 * e21

  i00 = elt2 E41 E41 x
  i01 = elt2 E41 E42 x
  i02 = elt2 E41 E43 x
  i03 = elt2 E41 E44 x
  e10 = elt2 E42 E41 x
  e11 = elt2 E42 E42 x
  e12 = elt2 E42 E43 x
  e13 = elt2 E42 E44 x
  e20 = elt2 E43 E41 x
  e21 = elt2 E43 E42 x
  e22 = elt2 E43 E43 x
  e23 = elt2 E43 E44 x
  e30 = elt2 E44 E41 x
  e31 = elt2 E44 E42 x
  e32 = elt2 E44 E43 x
  e33 = elt2 E44 E44 x
{-# INLINE det4 #-}

-- | 4x4 matrix inverse.
--
-- >>> row E41 . inv4 $ m44 1 0 3 2 2 0 2 1 0 0 0 1 0 3 4 0 :: V4 Rational
-- V4 (6 % (-12)) ((-9) % (-12)) ((-3) % (-12)) (0 % (-12))
--
inv4 :: Field a => M44 a -> M44 a
inv4 x = lscaleDef (recip det) $ x' where
  i00 = elt2 E41 E41 x
  i01 = elt2 E41 E42 x
  i02 = elt2 E41 E43 x
  i03 = elt2 E41 E44 x
  e10 = elt2 E42 E41 x
  e11 = elt2 E42 E42 x
  e12 = elt2 E42 E43 x
  e13 = elt2 E42 E44 x
  e20 = elt2 E43 E41 x
  e21 = elt2 E43 E42 x
  e22 = elt2 E43 E43 x
  e23 = elt2 E43 E44 x
  e30 = elt2 E44 E41 x
  e31 = elt2 E44 E42 x
  e32 = elt2 E44 E43 x
  e33 = elt2 E44 E44 x

  s0 = i00 * e11 - e10 * i01
  s1 = i00 * e12 - e10 * i02
  s2 = i00 * e13 - e10 * i03
  s3 = i01 * e12 - e11 * i02
  s4 = i01 * e13 - e11 * i03
  s5 = i02 * e13 - e12 * i03
  c5 = e22 * e33 - e32 * e23
  c4 = e21 * e33 - e31 * e23
  c3 = e21 * e32 - e31 * e22
  c2 = e20 * e33 - e30 * e23
  c1 = e20 * e32 - e30 * e22
  c0 = e20 * e31 - e30 * e21

  det = s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0

  x' = m44 (e11 * c5 - e12 * c4 + e13 * c3)
           (-i01 * c5 + i02 * c4 - i03 * c3)
           (e31 * s5 - e32 * s4 + e33 * s3)
           (-e21 * s5 + e22 * s4 - e23 * s3)
           (-e10 * c5 + e12 * c2 - e13 * c1)
           (i00 * c5 - i02 * c2 + i03 * c1)
           (-e30 * s5 + e32 * s2 - e33 * s1)
           (e20 * s5 - e22 * s2 + e23 * s1)
           (e10 * c4 - e11 * c2 + e13 * c0)
           (-i00 * c4 + i01 * c2 - i03 * c0)
           (e30 * s4 - e31 * s2 + e33 * s0)
           (-e20 * s4 + e21 * s2 - e23 * s0)
           (-e10 * c3 + e11 * c1 - e12 * c0)
           (i00 * c3 - i01 * c1 + i02 * c0)
           (-e30 * s3 + e31 * s1 - e32 * s0)
           (e20 * s3 - e21 * s1 + e22 * s0)
{-# INLINE inv4 #-}

-------------------------------------------------------------------------------
-- V1 instances
-------------------------------------------------------------------------------

instance Show1 V1 where
  liftShowsPrec f _ d (V1 a) = showParen (d >= 10) $ showString "V1 " . f d a

{-
instance Field a => Composition a V1 where
  conj = id

  norm f = unV1 $ liftA2 (*) f f
-}

instance Functor V1 where
  fmap f (V1 a) = V1 (f a)
  {-# INLINE fmap #-}
  a <$ _ = V1 a
  {-# INLINE (<$) #-}

instance Applicative V1 where
  pure = pureRep
  liftA2 = liftR2

instance Foldable V1 where
  foldMap f (V1 a) = f a
  {-# INLINE foldMap #-}
  null _ = False
  length _ = one

instance Foldable1 V1 where
  foldMap1 f (V1 a) = f a
  {-# INLINE foldMap1 #-}

instance Distributive V1 where
  distribute f = V1 $ fmap (\(V1 x) -> x) f
  {-# INLINE distribute #-}

instance Representable V1 where
  type Rep V1 = E1
  tabulate f = V1 (f E11)
  {-# INLINE tabulate #-}

  index (V1 x) E11 = x
  {-# INLINE index #-}

-------------------------------------------------------------------------------
-- V2 instances
-------------------------------------------------------------------------------


instance Show1 V2 where
  liftShowsPrec f _ d (V2 a b) = showsBinaryWith f f "V2" d a b

instance Functor V2 where
  fmap f (V2 a b) = V2 (f a) (f b)
  {-# INLINE fmap #-}
  a <$ _ = V2 a a
  {-# INLINE (<$) #-}

instance Applicative V2 where
  pure = pureRep
  liftA2 = liftR2

instance Foldable V2 where
  foldMap f (V2 a b) = f a <> f b
  {-# INLINE foldMap #-}
  null _ = False
  length _ = two

instance Foldable1 V2 where
  foldMap1 f (V2 a b) = f a <> f b
  {-# INLINE foldMap1 #-}

instance Distributive V2 where
  distribute f = V2 (fmap (\(V2 x _) -> x) f) (fmap (\(V2 _ y) -> y) f)
  {-# INLINE distribute #-}

instance Representable V2 where
  type Rep V2 = E2
  tabulate f = V2 (f E21) (f E22)
  {-# INLINE tabulate #-}

  index (V2 x _) E21 = x
  index (V2 _ y) E22 = y
  {-# INLINE index #-}

-------------------------------------------------------------------------------
-- V3 instances
-------------------------------------------------------------------------------


-- TODO add Prd1 and push instance downstream
instance Eq1 V3 where
  liftEq k (V3 a b c) (V3 d e f) = k a d && k b e && k c f

instance Show1 V3 where
  liftShowsPrec f _ d (V3 a b c) = showParen (d > 10) $
     showString "V3 " . f 11 a . showChar ' ' . f 11 b . showChar ' ' . f 11 c

instance Functor V3 where
  fmap f (V3 a b c) = V3 (f a) (f b) (f c)
  {-# INLINE fmap #-}
  a <$ _ = V3 a a a
  {-# INLINE (<$) #-}

instance Applicative V3 where
  pure = pureRep
  liftA2 = liftR2

instance Foldable V3 where
  foldMap f (V3 a b c) = f a <> f b <> f c
  {-# INLINE foldMap #-}
  null _ = False
  --length _ = 3

instance Foldable1 V3 where
  foldMap1 f (V3 a b c) = f a <> f b <> f c
  {-# INLINE foldMap1 #-}

instance Distributive V3 where
  distribute f = V3 (fmap (\(V3 x _ _) -> x) f) (fmap (\(V3 _ y _) -> y) f) (fmap (\(V3 _ _ z) -> z) f)
  {-# INLINE distribute #-}

instance Representable V3 where
  type Rep V3 = E3
  tabulate f = V3 (f E31) (f E32) (f E33)
  {-# INLINE tabulate #-}

  index (V3 x _ _) E31 = x
  index (V3 _ y _) E32 = y
  index (V3 _ _ z) E33 = z
  {-# INLINE index #-}

-------------------------------------------------------------------------------
-- V4 instances
-------------------------------------------------------------------------------


instance Show1 V4 where
  liftShowsPrec f _ z (V4 a b c d) = showParen (z > 10) $
     showString "V4 " . f 11 a . showChar ' ' . f 11 b . showChar ' ' . f 11 c . showChar ' ' . f 11 d

instance Functor V4 where
  fmap f (V4 a b c d) = V4 (f a) (f b) (f c) (f d)
  {-# INLINE fmap #-}
  a <$ _ = V4 a a a a
  {-# INLINE (<$) #-}

instance Applicative V4 where
  pure = pureRep
  liftA2 = liftR2

instance Foldable V4 where
  foldMap f (V4 a b c d) = f a <> f b <> f c <> f d
  {-# INLINE foldMap #-}
  null _ = False
  length _ = two + two

instance Foldable1 V4 where
  foldMap1 f (V4 a b c d) = f a <> f b <> f c <> f d
  {-# INLINE foldMap1 #-}

instance Distributive V4 where
  distribute f = V4 (fmap (\(V4 x _ _ _) -> x) f) (fmap (\(V4 _ y _ _) -> y) f) (fmap (\(V4 _ _ z _) -> z) f) (fmap (\(V4 _ _ _ w) -> w) f)
  {-# INLINE distribute #-}

instance Representable V4 where
  type Rep V4 = E4
  tabulate f = V4 (f E41) (f E42) (f E43) (f E44)
  {-# INLINE tabulate #-}

  index (V4 x _ _ _) E41 = x
  index (V4 _ y _ _) E42 = y
  index (V4 _ _ z _) E43 = z
  index (V4 _ _ _ w) E44 = w
  {-# INLINE index #-}


-------------------------------------------------------------------------------
-- Autogenerated instances
-------------------------------------------------------------------------------


#define deriveAdditiveSemigroup(ty)                                    \
instance (Additive-Semigroup) a => Semigroup (Additive (ty a)) where { \
   (<>) = liftA2 $ mzipWithRep (+)                                     \
;  {-# INLINE (<>) #-}                                                 \
}

#define deriveAdditiveMonoid(ty)                                 \
instance (Additive-Monoid) a => Monoid (Additive (ty a)) where { \
   mempty = pure $ pureRep zero                                  \
;  {-# INLINE mempty #-}                                         \
}

#define deriveMultiplicativeSemigroup(ty)                                    \
instance (Multiplicative-Semigroup) a => Semigroup (Multiplicative (ty a)) where { \
   (<>) = liftA2 $ mzipWithRep (*)                                     \
;  {-# INLINE (<>) #-}                                                 \
}

#define deriveMultiplicativeMonoid(ty)                                 \
instance (Multiplicative-Monoid) a => Monoid (Multiplicative (ty a)) where { \
   mempty = pure $ pureRep one                                  \
;  {-# INLINE mempty #-}                                         \
}

#define deriveMultiplicativeMatrixSemigroup(ty)                                    \
instance Semiring a => Semigroup (Multiplicative (ty a)) where { \
   (<>) = liftA2 $ (.#.)                                                           \
;  {-# INLINE (<>) #-}                                                             \
}

#define deriveMultiplicativeMatrixMonoid(ty)                                       \
instance Semiring a => Monoid (Multiplicative (ty a)) where {       \
   mempty = pure identity                                                          \
;  {-# INLINE mempty #-}                                                           \
}

#define deriveAdditiveMagma(ty)                                  \
instance (Additive-Group) a => Magma (Additive (ty a)) where {   \
   (<<) = liftA2 $ mzipWithRep (-)                               \
;  {-# INLINE (<<) #-}                                           \
}

#define deriveAdditiveQuasigroup(ty)                               \
instance (Additive-Group) a => Quasigroup (Additive (ty a)) \

#define deriveAdditiveLoop(ty)                               \
instance (Additive-Group) a => Loop (Additive (ty a)) \

#define deriveAdditiveGroup(ty)                               \
instance (Additive-Group) a => Group (Additive (ty a)) \

#define derivePresemiring(ty)              \
instance Semiring a => Presemiring (ty a)  \

#define deriveSemiring(ty)              \
instance Semiring a => Semiring (ty a)  \

#define deriveRing(ty)          \
instance Ring a => Ring (ty a)  \

#define deriveFreeLeftSemimodule(ty)                          \
instance Semiring a => LeftSemimodule a (ty a) where {        \
   lscale = lscaleDef                                         \
;  {-# INLINE lscale #-}                                      \
}

#define deriveFreeRightSemimodule(ty)                         \
instance Semiring a => RightSemimodule a (ty a) where {       \
   rscale = rscaleDef                                         \
;  {-# INLINE rscale #-}                                      \
}

#define deriveFreeBisemimodule(ty)                \
instance Semiring a => Bisemimodule a a (ty a)    \

#define deriveBisemimodule(tyl, tyr, ty)                      \
instance Semiring a => Bisemimodule (tyl a) (tyr a) (ty a)    \

#define deriveLeftSemimodule(tyl,ty)                          \
instance Semiring a => LeftSemimodule (tyl a) (ty a) where {  \
   lscale = (.#.)                                             \
;  {-# INLINE lscale #-}                                      \
}

#define deriveRightSemimodule(tyr,ty)                         \
instance Semiring a => RightSemimodule (tyr a) (ty a) where { \
   rscale = flip (.#.)                                        \
;  {-# INLINE rscale #-}                                      \
}

#define deriveBisemimodule(tyl, tyr, ty)                      \
instance Semiring a => Bisemimodule (tyl a) (tyr a) (ty a)    \



-- V1
deriveAdditiveSemigroup(V1)
deriveAdditiveMonoid(V1)

deriveAdditiveMagma(V1)
deriveAdditiveQuasigroup(V1)
deriveAdditiveLoop(V1)
deriveAdditiveGroup(V1)

deriveFreeLeftSemimodule(V1)
deriveFreeRightSemimodule(V1)
deriveFreeBisemimodule(V1)


-- V2
deriveAdditiveSemigroup(V2)
deriveAdditiveMonoid(V2)

deriveAdditiveMagma(V2)
deriveAdditiveQuasigroup(V2)
deriveAdditiveLoop(V2)
deriveAdditiveGroup(V2)

deriveFreeLeftSemimodule(V2)
deriveFreeRightSemimodule(V2)
deriveFreeBisemimodule(V2)


-- V3
deriveAdditiveSemigroup(V3)
deriveAdditiveMonoid(V3)

deriveAdditiveMagma(V3)
deriveAdditiveQuasigroup(V3)
deriveAdditiveLoop(V3)
deriveAdditiveGroup(V3)

deriveFreeLeftSemimodule(V3)
deriveFreeRightSemimodule(V3)
deriveFreeBisemimodule(V3)

-- V4
deriveAdditiveSemigroup(V4)
deriveAdditiveMonoid(V4)

deriveAdditiveMagma(V4)
deriveAdditiveQuasigroup(V4)
deriveAdditiveLoop(V4)
deriveAdditiveGroup(V4)

deriveFreeLeftSemimodule(V4)
deriveFreeRightSemimodule(V4)
deriveFreeBisemimodule(V4)

-- M11
deriveAdditiveSemigroup(M11)
deriveAdditiveMonoid(M11)

deriveAdditiveMagma(M11)
deriveAdditiveQuasigroup(M11)
deriveAdditiveLoop(M11)
deriveAdditiveGroup(M11)

deriveLeftSemimodule(M11, M11)
deriveRightSemimodule(M11, M11)
deriveBisemimodule(M11, M11, M11)

deriveMultiplicativeMatrixSemigroup(M11)
deriveMultiplicativeMatrixMonoid(M11)

derivePresemiring(M11)
deriveSemiring(M11)
deriveRing(M11)

-- M21
deriveAdditiveSemigroup(M21)
deriveAdditiveMonoid(M21)

deriveAdditiveMagma(M21)
deriveAdditiveQuasigroup(M21)
deriveAdditiveLoop(M21)
deriveAdditiveGroup(M21)

deriveLeftSemimodule(M22, M21)
deriveRightSemimodule(M11, M21)
deriveBisemimodule(M22, M11, M21)


-- M31
deriveAdditiveSemigroup(M31)
deriveAdditiveMonoid(M31)

deriveAdditiveMagma(M31)
deriveAdditiveQuasigroup(M31)
deriveAdditiveLoop(M31)
deriveAdditiveGroup(M31)

deriveLeftSemimodule(M33, M31)
deriveRightSemimodule(M11, M31)
deriveBisemimodule(M33, M11, M31)


-- M41
deriveAdditiveSemigroup(M41)
deriveAdditiveMonoid(M41)

deriveAdditiveMagma(M41)
deriveAdditiveQuasigroup(M41)
deriveAdditiveLoop(M41)
deriveAdditiveGroup(M41)

deriveLeftSemimodule(M44, M41)
deriveRightSemimodule(M11, M41)
deriveBisemimodule(M44, M11, M41)


-- M12
deriveAdditiveSemigroup(M12)
deriveAdditiveMonoid(M12)

deriveAdditiveMagma(M12)
deriveAdditiveQuasigroup(M12)
deriveAdditiveLoop(M12)
deriveAdditiveGroup(M12)

deriveLeftSemimodule(M11, M12)
deriveRightSemimodule(M22, M12)
deriveBisemimodule(M11, M22, M12)


-- M22
deriveAdditiveSemigroup(M22)
deriveAdditiveMonoid(M22)

deriveAdditiveMagma(M22)
deriveAdditiveQuasigroup(M22)
deriveAdditiveLoop(M22)
deriveAdditiveGroup(M22)

deriveLeftSemimodule(M22, M22)
deriveRightSemimodule(M22, M22)
deriveBisemimodule(M22, M22, M22)

deriveMultiplicativeMatrixSemigroup(M22)
deriveMultiplicativeMatrixMonoid(M22)

derivePresemiring(M22)
deriveSemiring(M22)
deriveRing(M22)


-- M32
deriveAdditiveSemigroup(M32)
deriveAdditiveMonoid(M32)

deriveAdditiveMagma(M32)
deriveAdditiveQuasigroup(M32)
deriveAdditiveLoop(M32)
deriveAdditiveGroup(M32)

deriveLeftSemimodule(M33, M32)
deriveRightSemimodule(M22, M32)
deriveBisemimodule(M33, M22, M32)


-- M42
deriveAdditiveSemigroup(M42)
deriveAdditiveMonoid(M42)

deriveAdditiveMagma(M42)
deriveAdditiveQuasigroup(M42)
deriveAdditiveLoop(M42)
deriveAdditiveGroup(M42)

deriveLeftSemimodule(M44, M42)
deriveRightSemimodule(M22, M42)
deriveBisemimodule(M44, M22, M42)


-- M13
deriveAdditiveSemigroup(M13)
deriveAdditiveMonoid(M13)

deriveAdditiveMagma(M13)
deriveAdditiveQuasigroup(M13)
deriveAdditiveLoop(M13)
deriveAdditiveGroup(M13)

deriveLeftSemimodule(M11, M13)
deriveRightSemimodule(M33, M13)
deriveBisemimodule(M11, M33, M13)


-- M23
deriveAdditiveSemigroup(M23)
deriveAdditiveMonoid(M23)

deriveAdditiveMagma(M23)
deriveAdditiveQuasigroup(M23)
deriveAdditiveLoop(M23)
deriveAdditiveGroup(M23)

deriveLeftSemimodule(M22, M23)
deriveRightSemimodule(M33, M23)
deriveBisemimodule(M22, M33, M23)


-- M33
deriveAdditiveSemigroup(M33)
deriveAdditiveMonoid(M33)

deriveAdditiveMagma(M33)
deriveAdditiveQuasigroup(M33)
deriveAdditiveLoop(M33)
deriveAdditiveGroup(M33)

deriveLeftSemimodule(M33, M33)
deriveRightSemimodule(M33, M33)
deriveBisemimodule(M33, M33, M33)

deriveMultiplicativeMatrixSemigroup(M33)
deriveMultiplicativeMatrixMonoid(M33)

derivePresemiring(M33)
deriveSemiring(M33)
deriveRing(M33)


-- M43
deriveAdditiveSemigroup(M43)
deriveAdditiveMonoid(M43)

deriveAdditiveMagma(M43)
deriveAdditiveQuasigroup(M43)
deriveAdditiveLoop(M43)
deriveAdditiveGroup(M43)

deriveLeftSemimodule(M44, M43)
deriveRightSemimodule(M33, M43)
deriveBisemimodule(M44, M33, M43)


-- M14
deriveAdditiveSemigroup(M14)
deriveAdditiveMonoid(M14)

deriveAdditiveMagma(M14)
deriveAdditiveQuasigroup(M14)
deriveAdditiveLoop(M14)
deriveAdditiveGroup(M14)

deriveLeftSemimodule(M11, M14)
deriveRightSemimodule(M44, M14)
deriveBisemimodule(M11, M44, M14)


-- M24
deriveAdditiveSemigroup(M24)
deriveAdditiveMonoid(M24)

deriveAdditiveMagma(M24)
deriveAdditiveQuasigroup(M24)
deriveAdditiveLoop(M24)
deriveAdditiveGroup(M24)

deriveLeftSemimodule(M22, M24)
deriveRightSemimodule(M44, M24)
deriveBisemimodule(M22, M44, M24)


-- M34
deriveAdditiveSemigroup(M34)
deriveAdditiveMonoid(M34)

deriveAdditiveMagma(M34)
deriveAdditiveQuasigroup(M34)
deriveAdditiveLoop(M34)
deriveAdditiveGroup(M34)

deriveLeftSemimodule(M33, M34)
deriveRightSemimodule(M44, M34)
deriveBisemimodule(M33, M44, M34)


-- M44
deriveAdditiveSemigroup(M44)
deriveAdditiveMonoid(M44)

deriveAdditiveMagma(M44)
deriveAdditiveQuasigroup(M44)
deriveAdditiveLoop(M44)
deriveAdditiveGroup(M44)

deriveLeftSemimodule(M44, M44)
deriveRightSemimodule(M44, M44)
deriveBisemimodule(M44, M44, M44)

deriveMultiplicativeMatrixSemigroup(M44)
deriveMultiplicativeMatrixMonoid(M44)

derivePresemiring(M44)
deriveSemiring(M44)
deriveRing(M44)
