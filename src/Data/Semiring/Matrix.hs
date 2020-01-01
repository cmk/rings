{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE Safe #-}

-- | API essentially follows that of /linear/ & /hmatrix/.
module Data.Semiring.Matrix (
    type M22
  , type M23
  , type M24
  , type M32
  , type M33
  , type M34
  , type M42
  , type M43
  , type M44
  , m22
  , m23
  , m24
  , m32
  , m33
  , m34
  , m42
  , m43
  , m44
  , row
  , col
  , (.>)
  , (<.)
  , (#>)
  , (<#)
  , (<#>)
  , scale
  , identity
  , transpose
  , trace
  , diag
  , bdet2
  , det2
  , det2d
  , inv2d
  , bdet3
  , det3
  , det3d
  , inv3d
  , bdet4
  , det4
  , det4d
  , inv4d
  ) where

import safe Data.Distributive
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Functor.Compose
import safe Data.Functor.Rep
import safe Data.Group
import safe Data.Prd
import safe Data.Ring
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Semiring
import safe Data.Semiring.Module
import safe Data.Semiring.V2
import safe Data.Semiring.V3
import safe Data.Semiring.V4
import safe Data.Tuple

import safe Prelude hiding (sum, negate)

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

-- | Construct a 2x2 matrix.
--
-- Arguments are in row-major order.
--
m22 :: a -> a -> a -> a -> M22 a
m22 a b c d = V2 (V2 a b) (V2 c d)
{-# INLINE m22 #-}

-- | Construct a 2x3 matrix.
--
-- Arguments are in row-major order.
--
m23 :: a -> a -> a -> a -> a -> a -> M23 a
m23 a b c d e f = V2 (V3 a b c) (V3 d e f)
{-# INLINE m23 #-}

-- | Construct a 2x4 matrix.
--
-- Arguments are in row-major order.
--
m24 :: a -> a -> a -> a -> a -> a -> a -> a -> M24 a
m24 a b c d e f g h = V2 (V4 a b c d) (V4 e f g h)
{-# INLINE m24 #-}

-- | Construct a 3x2 matrix.
--
-- Arguments are in row-major order.
--
m32 :: a -> a -> a -> a -> a -> a -> M32 a
m32 a b c d e f = V3 (V2 a b) (V2 c d) (V2 e f)
{-# INLINE m32 #-}

-- | Construct a 3x3 matrix.
--
-- Arguments are in row-major order.
--
m33 :: a -> a -> a -> a -> a -> a -> a -> a -> a -> M33 a
m33 a b c d e f g h i = V3 (V3 a b c) (V3 d e f) (V3 g h i)
{-# INLINE m33 #-}

-- | Construct a 3x4 matrix.
--
-- Arguments are in row-major order.
--
m34 :: a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> M34 a
m34 a b c d e f g h i j k l = V3 (V4 a b c d) (V4 e f g h) (V4 i j k l)
{-# INLINE m34 #-}

-- | Construct a 4x2 matrix.
--
-- Arguments are in row-major order.
--
m42 :: a -> a -> a -> a -> a -> a -> a -> a -> M42 a
m42 a b c d e f g h = V4 (V2 a b) (V2 c d) (V2 e f) (V2 g h)
{-# INLINE m42 #-}

-- | Construct a 4x3 matrix.
--
-- Arguments are in row-major order.
--
m43 :: a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> M43 a
m43 a b c d e f g h i j k l = V4 (V3 a b c) (V3 d e f) (V3 g h i) (V3 j k l)
{-# INLINE m43 #-}

-- | Construct a 4x4 matrix.
--
-- Arguments are in row-major order.
--
m44 :: a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> a -> M44 a
m44 a b c d e f g h i j k l m n o p = V4 (V4 a b c d) (V4 e f g h) (V4 i j k l) (V4 m n o p)
{-# INLINE m44 #-}

-- | Index into a row of a matrix or vector.
--
-- >>> row I21 (V2 1 2)
-- 1
--
row :: Representable f => Rep f -> f c -> c
row i = flip index i
{-# INLINE row #-}

-- | Index into a column of a matrix.
--
-- >>> row I22 . col I31 $ V2 (V3 1 2 3) (V3 4 5 6)
-- 4
--
col :: Functor f => Representable g => Rep g -> f (g a) -> f a
col j m = flip index j $ distribute m
{-# INLINE col #-}

infixl 7 <.

-- | Matrix-scalar product.
--
-- The /</ arrow points towards the return type.
--
-- >>> m22 1 2 3 4 <. 5
-- V2 (V2 5 10) (V2 15 20)
--
-- >>> m22 1 2 3 4 <. 5 <. 2
-- V2 (V2 10 20) (V2 30 40)
--
(<.) :: Semiring a => Functor f => Functor g => f (g a) -> a -> f (g a)
f <. a = fmap (fmap (>< a)) f
{-# INLINE (<.) #-}

infixr 7 .>

-- | Scalar-matrix product.
--
-- The />/ arrow points towards the return type.
--
-- >>> 5 .> V2 (V2 1 2) (V2 3 4)
-- V2 (V2 5 10) (V2 15 20)
--
(.>) :: Semiring a => Functor f => Functor g => a -> f (g a) -> f (g a)
(.>) a = fmap (fmap (a ><))
{-# INLINE (.>) #-}

infixl 7 <#

-- | Multiply a matrix on the left by a row vector.
--
-- >>> V2 1 2 <# m23 3 4 5 6 7 8
-- V3 15 18 21
--
-- >>> V2 1 2 <# m23 3 4 5 6 7 8 <# m32 1 0 0 0 0 0
-- V2 15 0
--
(<#) :: (Semiring a, Free f, Free g) => f a -> f (g a) -> g a
x <# y = tabulate (\j -> x <.> col j y)
{-# INLINE (<#) #-}

infixr 7 #>, <#>

-- | Multiply a matrix on the right by a column vector.
--
-- >>> m23 1 2 3 4 5 6 #> V3 7 8 9
-- V2 50 122
--
-- >>> m22 1 0 0 0 #> m23 1 2 3 4 5 6 #> V3 7 8 9
-- V2 50 0
--
(#>) :: (Semiring a, Free f, Free g) => f (g a) -> g a -> f a
x #> y = tabulate (\i -> row i x <.> y)
{-# INLINE (#>) #-}

-- | Multiply two matrices.
--
-- >>> m22 1 2 3 4 <#> m22 1 2 3 4 :: M22 Int
-- V2 (V2 7 10) (V2 15 22)
-- 
-- >>> m23 1 2 3 4 5 6 <#> m32 1 2 3 4 4 5 :: M22 Int
-- V2 (V2 19 25) (V2 43 58)
--
(<#>) :: (Semiring a, Free f, Free g, Free h) => f (g a) -> g (h a) -> f (h a)
(<#>) x y = getCompose $ tabulate (\(i,j) -> row i x <.> col j y)
{-# INLINE (<#>) #-}

-- | Obtain a diagonal matrix from a vector.
--
-- >>> scale (V2 2 3)
-- V2 (V2 2 0) (V2 0 3)
--
scale :: Monoid a => Free f => f a -> f (f a)
scale f = flip imapRep f $ \i x -> flip imapRep f (\j _ -> if i == j then x else mempty)
{-# INLINE scale #-}

-- | Identity matrix.
--
-- >>> identity :: M44 Int
-- V4 (V4 1 0 0 0) (V4 0 1 0 0) (V4 0 0 1 0) (V4 0 0 0 1)
--
-- >>> identity :: V3 (V3 Int)
-- V3 (V3 1 0 0) (V3 0 1 0) (V3 0 0 1)
--
identity :: Unital a => Free f => f (f a)
identity = scale $ pureRep sunit
{-# INLINE identity #-}

-- | Transpose a matrix.
--
-- > transpose (V3 (V2 1 2) (V2 3 4) (V2 5 6))
-- V2 (V3 1 3 5) (V3 2 4 6)
--
transpose :: Functor f => Distributive g => f (g a) -> g (f a)
transpose = distribute
{-# INLINE transpose #-}

-- | Compute the trace of a matrix.
--
-- >>> trace (V2 (V2 a b) (V2 c d))
-- a <> d
--
trace :: Semigroup a => Free f => f (f a) -> a
trace = Foldable1.fold1 . diag
{-# INLINE trace #-}

-- | Compute the diagonal of a matrix.
--
-- >>> diagonal (V2 (V2 a b) (V2 c d))
-- V2 a d
--
diag :: Representable f => f (f a) -> f a
diag = flip bindRep id
{-# INLINE diag #-}

-- | 2x2 matrix bideterminant over a commutative semiring.
--
-- >>> bdet2 $ m22 1 2 3 4
-- (4,6)
--
bdet2 :: Semiring a => M22 a -> (a, a)
bdet2 (V2 (V2 a b) (V2 c d)) = (a >< d, b >< c)
{-# INLINE bdet2 #-}

-- | 2x2 matrix determinant over a commutative ring.
--
-- @
-- 'det2' ≡ 'uncurry' ('<<') . 'bdet2'
-- @
--
det2 :: Ring a => M22 a -> a
det2 = uncurry (<<) . bdet2
{-# INLINE det2 #-}

-- | 2x2 double-precision matrix determinant.
--
-- >>> det2d $ m22 1 2 3 4
-- -2.0
--
det2d :: M22 Double -> Double
det2d (V2 (V2 a b) (V2 c d)) = a * d - b * c
{-# INLINE det2d #-}

-- | 2x2 double-precision matrix inverse.
--
-- >>> inv2d $ m22 1 2 3 4
-- V2 (V2 (-2.0) 1.0) (V2 1.5 (-0.5))
--
inv2d :: M22 Double -> M22 Double
inv2d m@(V2 (V2 a b) (V2 c d)) = (1 / det2d m) .> m22 d (-b) (-c) a
{-# INLINE inv2d #-}

-- | 3x3 matrix bideterminant over a commutative semiring.
--
-- >>> bdet3 (V3 (V3 1 2 3) (V3 4 5 6) (V3 7 8 9))
-- (225, 225)
--
bdet3 :: Semiring a => M33 a -> (a, a)
bdet3 (V3 (V3 a b c) (V3 d e f) (V3 g h i)) = (evens, odds)
  where
    evens = a><e><i <> g><b><f <> d><h><c
    odds  = a><h><f <> d><b><i <> g><e><c
{-# INLINE bdet3 #-}

-- | 3x3 matrix determinant over a commutative ring.
--
-- @
-- 'det3' ≡ 'uncurry' ('<<') . 'bdet3'
-- @
--
det3 :: Ring a => M33 a -> a
det3 = uncurry (<<) . bdet3
{-# INLINE det3 #-}

-- | 3x3 double-precision matrix determinant.
--
-- This implementation uses a cofactor expansion to avoid loss of precision.
--
det3d :: M33 Double -> Double
det3d (V3 (V3 a b c)
          (V3 d e f)
          (V3 g h i)) = a * (e*i-f*h) - d * (b*i-c*h) + g * (b*f-c*e)
{-# INLINE det3d #-}

-- | 3x3 double-precision matrix inverse.
--
-- >>> inv3d $ m33 1 2 4 4 2 2 1 1 1
-- V3 (V3 0.0 0.5 (-1.0)) (V3 (-0.5) (-0.75) 3.5) (V3 0.5 0.25 (-1.5))
--
inv3d :: M33 Double -> M33 Double
inv3d m@(V3 (V3 a b c)
            (V3 d e f)
            (V3 g h i)) =
  let a' = cofactor (e,f,h,i)
      b' = cofactor (c,b,i,h)
      c' = cofactor (b,c,e,f)
      d' = cofactor (f,d,i,g)
      e' = cofactor (a,c,g,i)
      f' = cofactor (c,a,f,d)
      g' = cofactor (d,e,g,h)
      h' = cofactor (b,a,h,g)
      i' = cofactor (a,b,d,e)
      cofactor (q,r,s,t) = det2d $ m22 q r s t
      det = det3d m
   in (1 / det) .> m33 a' b' c' d' e' f' g' h' i'
{-# INLINE inv3d #-}

-- | 4x4 matrix bideterminant over a commutative semiring.
--
-- >>> bdet4 (V4 (V4 1 2 3 4) (V4 5 6 7 8) (V4 9 10 11 12) (V4 13 14 15 16))
-- (27728,27728)
--
bdet4 :: Semiring a => M44 a -> (a, a)
bdet4 (V4 (V4 a b c d) (V4 e f g h) (V4 i j k l) (V4 m n o p)) = (evens, odds)
  where
    evens = a >< (f><k><p <> g><l><n <> h><j><o) <>
            b >< (g><i><p <> e><l><o <> h><k><m) <>
            c >< (e><j><p <> f><l><m <> h><i><n) <>
            d >< (f><i><o <> e><k><n <> g><j><m)

    odds =  a >< (g><j><p <> f><l><o <> h><k><n) <>
            b >< (e><k><p <> g><l><m <> h><i><o) <>
            c >< (f><i><p <> e><l><n <> h><j><m) <>
            d >< (e><j><o <> f><k><m <> g><i><n)
{-# INLINE bdet4 #-}

-- | 4x4 matrix determinant over a commutative ring.
--
-- @
-- 'det4' ≡ 'uncurry' ('<<') . 'bdet4'
-- @
--
det4 :: Ring a => M44 a -> a
det4 = uncurry (<<) . bdet4
{-# INLINE det4 #-}

-- | 4x4 double-precision matrix determinant.
--
-- This implementation uses a cofactor expansion to avoid loss of precision.
--
det4d :: M44 Double -> Double
det4d (V4 (V4 i00 i01 i02 i03)
          (V4 i10 i11 i12 i13)
          (V4 i20 i21 i22 i23)
          (V4 i30 i31 i32 i33)) =
  let
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
  in s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0
{-# INLINE det4d #-}

-- | 4x4 double-precision matrix inverse.
--
inv4d :: M44 Double -> M44 Double
inv4d (V4 (V4 i00 i01 i02 i03)
          (V4 i10 i11 i12 i13)
          (V4 i20 i21 i22 i23)
          (V4 i30 i31 i32 i33)) =
  let s0 = i00 * i11 - i10 * i01
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
      invDet = recip det
   in invDet .> V4 (V4 (i11 * c5 - i12 * c4 + i13 * c3)
                       (-i01 * c5 + i02 * c4 - i03 * c3)
                       (i31 * s5 - i32 * s4 + i33 * s3)
                       (-i21 * s5 + i22 * s4 - i23 * s3))
                   (V4 (-i10 * c5 + i12 * c2 - i13 * c1)
                       (i00 * c5 - i02 * c2 + i03 * c1)
                       (-i30 * s5 + i32 * s2 - i33 * s1)
                       (i20 * s5 - i22 * s2 + i23 * s1))
                   (V4 (i10 * c4 - i11 * c2 + i13 * c0)
                       (-i00 * c4 + i01 * c2 - i03 * c0)
                       (i30 * s4 - i31 * s2 + i33 * s0)
                       (-i20 * s4 + i21 * s2 - i23 * s0))
                   (V4 (-i10 * c3 + i11 * c1 - i12 * c0)
                       (i00 * c3 - i01 * c1 + i02 * c0)
                       (-i30 * s3 + i31 * s1 - i32 * s0)
                       (i20 * s3 - i21 * s1 + i22 * s0))
{-# INLINE inv4d #-}
