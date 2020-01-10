{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Module.Quaternion where

import safe Data.Complex
import safe Data.Dioid
import safe Data.Distributive
import safe Data.Field
import safe Data.Functor.Rep
import safe Data.Group
import safe Data.Module
import safe Data.Module.Matrix
import safe Data.Module.V3
import safe Data.Ring
import safe Data.Semigroup.Foldable
import safe GHC.Generics

import safe Prelude hiding (Num(..), Fractional(..), product)
import safe qualified Prelude as N

import GHC.Real hiding (Fractional(..))
import Data.Fixed

data Quaternion a = Quaternion !a {-# UNPACK #-}! (V3 a) deriving (Eq, Ord, Show, Generic, Generic1)

type QuatF = Quaternion Float
type QuatD = Quaternion Double
type QuatR = Quaternion Rational
type QuatM = Quaternion Micro
type QuatN = Quaternion Nano
type QuatP = Quaternion Pico

{-
-- centi
λ> iter4 q1 (V3 1 0 0)
V3 0.93 -0.01 0.00
-- micro, same precision as Double
λ> iter4 q1 (V3 1 0 0)
V3 0.999925 0.000001 0.000000
-}


{-
TODO: need to normalize if we can rotate w/ unnormalized quats?

-- | Obtain a idx length 'Quaternion' representing a rotation of @angle@ radians about @axis@.
--
-- See < https://en.wikipedia.org/wiki/Axis%E2%80%93angle_representation >
--
axisAngle ::  V3 Double -> Double -> QuatD
axisAngle axis angle = Quaternion (cos $ angle / 2) $ fmap (sin (angle / 2) ><) axis
{-# INLINE axisAngle #-}
-}

-- | Obtain a 'Quaternion' from 4 base field elements.
--
quat :: a -> a -> a -> a -> Quaternion a
quat r x y z = Quaternion r (V3 x y z)

-- | Real or scalar part of a quaternion.
--
real :: Quaternion a -> a
real (Quaternion r _) = r

-- | Imaginary or vector part of a quaternion.
--
imag :: Quaternion a -> V3 a
imag (Quaternion _ v) = v

-- | Squared norm of a quaternion.
--
-- @ norm x == real $ x >< conj x @
--
norm :: Semiring a => Quaternion a -> a
norm (Quaternion r v) = r >< r <> quadrance v

normalize :: QuatD -> QuatD
normalize q = fmap (nrm ><) q where nrm = N.sqrt . N.recip . norm $ q

-- | Use a quaternion to rotate a vector.
--
-- rotate qk . rotate qj $ V3 1 1 0
-- V3 1 (-1) 0
--
rotate :: Ring a => Quaternion a -> V3 a -> V3 a
rotate q v = ijk where Quaternion _ ijk = q >< Quaternion mempty v >< conj q

-- TODO: add to Property module
-- conj == conj'
-- conj' :: QuatR -> QuatR
-- conj' q = negate (recip 2) >< (q <> (i >< q >< i) <> (j >< q >< j) <> (k >< q >< k))

{- need tolerances:
λ> prop_conj q12 (q3 :: QuatP)
False
λ> prop_conj q14 (q3 :: QuatP)
False
-}
prop_conj :: Ring a => (a -> a -> Bool) -> Quaternion a -> Quaternion a -> Bool
prop_conj (~~) p q = productWith id $ mzipWithRep (~~) (conj (p >< q)) (conj q >< conj p)

-- conj (p >< q) = conj q >< conj p
-- conj q = (-0.5) >< (q <> (i >< q >< i) <> (j >< q >< j) <> (k >< q >< k))
-- 2 >< real q ≡ q <> conj q
-- 2 >< imag q ≡ q << conj q
conj :: Group a => Quaternion a -> Quaternion a
conj (Quaternion r v) = Quaternion r $ fmap negate v

-------------------------------------------------------------------------------
-- Useful quaternions
-------------------------------------------------------------------------------

-- | The /i/ quaternion.
--
-- Represents a \( \pi \) radian rotation about the /x/ axis.
--
-- >>> rotate (qi :: QuatM) $ V3 1 0 0
-- V3 1.000000 0.000000 0.000000
-- >>> rotate (qi :: QuatM) $ V3 0 1 0
-- V3 0.000000 -1.000000 0.000000
-- >>> rotate (qi :: QuatM) $ V3 0 0 1
-- V3 0.000000 0.000000 -1.000000
--
-- >>> qi >< qj
-- Quaternion 0 (V3 0 0 1)
--
qi :: Unital a => Quaternion a
qi = Quaternion mempty $ idx I31

-- | The /j/ quaternion.
--
-- Represents a \( \pi \) radian rotation about the /y/ axis.
--
-- >>> rotate (qj :: QuatM) $ V3 1 0 0
-- V3 -1.000000 0.000000 0.000000
-- >>> rotate (qj :: QuatM) $ V3 0 1 0
-- V3 0.000000 1.000000 0.000000
-- >>> rotate (qj :: QuatM) $ V3 0 0 1
-- V3 0.000000 0.000000 -1.000000
--
-- >>> qj >< qk
-- Quaternion 0 (V3 1 0 0)
--
qj :: Unital a => Quaternion a
qj = Quaternion mempty $ idx I32

-- | The /k/ quaternion.
--
-- Represents a \( \pi \) radian rotation about the /z/ axis.
--
-- >>> rotate (qk :: QuatM) $ V3 1 0 0
-- V3 -1.000000 0.000000 0.000000
-- >>> rotate (qk :: QuatM) $ V3 0 1 0
-- V3 0.000000 -1.000000 0.000000
-- >>> rotate (qk :: QuatM) $ V3 0 0 1
-- V3 0.000000 0.000000 1.000000
--
-- >>> qk >< qi
-- Quaternion 0 (V3 0 1 0)
-- >>> qi >< qj >< qk
-- Quaternion (-1) (V3 0 0 0)
--
qk :: Unital a => Quaternion a
qk = Quaternion mempty $ idx I33


-- TODO place in doctest preamble
cosAngle :: QuatP -> V3 Pico -> Pico
cosAngle q v = v <.> (rotate q v)

-- | Identity (empty) rotation.
--
-- All rotations written according to the < https://en.wikipedia.org/wiki/Right-hand_rule right-hand rule >.
--
q00 :: Field a => Quaternion a
q00 = sunit

-- | A \( \pi/2 \) radian rotation about the /y/ axis.
--
-- >>> m33 0 0 1 0 1 0 (-1) 0 0 #> V3 0 1 0 :: V3 Micro
-- V3 0.000000 1.000000 0.000000
--
q01 :: Field a => Quaternion a
q01 = quat irt2 0 irt2 0

-- | A \( \pi \) radian rotation about the /y/ axis.
--
q02 :: Field a => Quaternion a 
q02 = qj

-- | A \( 3 \pi/2 \) radian rotation about the /y/ axis.
--
q03 :: Field a => Quaternion a 
q03 = quat irt2 0 (-irt2) 0

-- | A \( \pi/2 \) radian rotation about the /z/ axis.
--
-- >>> rotate (q04 :: QuatM) $ V3 0 0 1
-- V3 0.000000 0.000000 0.999996
-- >>> rotate (q04 :: QuatM) $ V3 1 1 0
-- V3 -0.999998 0.999997 0.000000
--
q04 :: Field a => Quaternion a 
q04 = quat irt2 0 0 irt2

-- | A \( 2 \pi/3 \) radian rotation about the /x-y-z/ axis.
--
-- @ q05 ≡ q01 >< q04 @
--
-- >>> rotate (q05 :: QuatM) $ V3 1 1 1
-- V3 1.000000 1.000000 1.000000
-- >>> cosAngle q05 (fmap (irt2><) $ V3 1 (-1) 0)
-- -0.499999999991
-- >>> cosAngle q05 (fmap (irt2><) $ V3 0 1 (-1))
-- -0.499999999991
-- >>> cosAngle q05 (fmap (irt2><irt3><) $ V3 1 (-2) 1)
-- -0.499999999993
--
q05 :: Field a => Quaternion a 
q05 = quat 0.5 0.5 0.5 0.5

-- | A \( \pi \) radian rotation about the /x-y/ axis.
--
-- @ q06 ≡ q02 >< q04 @
--
-- >>> rotate (q06 :: QuatM) $ V3 1 1 0
-- V3 0.999997 0.999997 0.000000
-- >>> rotate (q06 :: QuatM) $ V3 0 0 1
-- V3 0.000000 0.000000 -0.999997
--
q06 :: Field a => Quaternion a 
q06 = quat 0 irt2 irt2 0

-- | A \( 2 \pi/3 \) radian rotation about the /(-x)-(-y)-z/ axis.
--
-- Equivalent to a \( 3 \pi/2 \) radian rotation about y axis,
-- followed by \( \pi/2 \) radian rotation about z axis:
--
-- @ q07 ≡ q03 >< q04 @
--
-- >>> rotate (q07 :: QuatM) $ V3 1 1 (-1)
-- V3 1.000000 1.000000 -1.000000
-- >>> cosAngle q07 ((irt2><irt3><) <$> V3 (-1) 2 1)
-- -0.499999999993
--
q07 :: Field a => Quaternion a
q07 = quat 0.5 (-0.5) (-0.5) 0.5

-- | A \( 3 \pi/2 \) radian rotation about the /z/ axis.
--
-- >>> rotate (q08 :: QuatM) $ V3 0 0 1
-- V3 0.000000 0.000000 0.999996
-- >>> rotate (q08 :: QuatM) $ V3 1 1 0
-- V3 0.999997 -0.999997 0.000000
--
q08 :: Field a => Quaternion a
q08 = quat irt2 0 0 (-irt2)

-- | A \( 2 \pi/3 \) radian rotation about the /(-x)-y-(-z)/ axis.
--
-- @ q09 ≡ q01 >< q08 @
--
-- >>> rotate (q09 :: QuatM) $ V3 1 (-1) 1
-- V3 1.000000 -1.000000 1.000000
-- >>> cosAngle q09 ((irt2><irt3><) <$> V3 1 2 1)
-- -0.499999999993
--
q09 :: Field a => Quaternion a
q09 = quat 0.5 (-0.5) 0.5 (-0.5)

-- |
-- @ q10 ≡ q02 >< q08 @
--
q10 :: Field a => Quaternion a
q10 = quat 0 (-irt2) irt2 0

-- | A \( 2 \pi/3 \) radian rotation about the /x-(-y)-(-z)/ axis.
--
-- @ q11 ≡ q03 >< q08 @
--
-- >>> rotate (q11 :: QuatM) $ V3 (-1) 1 1
-- V3 1.000000 1.000000 -1.000000
-- >>> cosAngle q11 ((irt2><irt3><) <$> V3 1 2 (-1))
-- -0.499999999993
--
q11 :: Field a => Quaternion a
q11 = quat 0.5 0.5 (-0.5) (-0.5)

-- | A \( \pi/2 \) radian rotation about the /x/ axis.
--
-- >>> rotate (q12 :: QuatM) $ V3 1 0 0
-- V3 0.999996 0.000000 0.000000
-- >>> rotate (q12 :: QuatM) $ V3 0 1 1
-- V3 0.000000 -0.999998 0.999997
-- 
q12 :: Field a => Quaternion a
q12 = quat irt2 irt2 0 0

-- |
-- 
-- @ q13 ≡ q01 >< q12 @
--
q13 :: Field a => Quaternion a
q13 = quat 0.5 0.5 0.5 (-0.5)

-- |
--
-- @ q14 ≡ q02 >< q12 @
-- 
q14 :: Field a => Quaternion a
q14 = quat 0 0 irt2 (-irt2)

-- |
--
-- @ q15 ≡ q03 >< q12 @
--
q15 :: Field a => Quaternion a
q15 = quat 0.5 0.5 (-0.5) 0.5

-- | A \( \pi \) radian rotation about the /x/ axis.
--
-- λ> rotate (q16 :: QuatM) $ V3 1 0 0
-- V3 1.000000 0.000000 0.000000
-- λ> rotate (q16 :: QuatM) $ V3 0 1 1
-- V3 0.000000 -1.000000 -1.000000
-- 
q16 :: Field a => Quaternion a
q16 = qi

-- |
--
-- @ q17 ≡ q01 >< q16 @
--
q17 :: Field a => Quaternion a
q17 = quat 0 irt2 0 (-irt2)

-- |
--
-- @ q18 ≡ q02 >< q16 @
--
q18 :: Field a => Quaternion a
q18 = conj qk

-- |
--
-- @ q19 ≡ q03 >< q16 @
--
q19 :: Field a => Quaternion a
q19 = quat 0 irt2 0 irt2

-- | A \( 3 \pi/2 \) radian rotation about the /x/ axis.
--
-- >>> rotate (q20 :: QuatM) $ V3 1 0 0
-- V3 0.999996 0.000000 0.000000
-- >>> rotate (q20 :: QuatM) $ V3 0 1 1
-- V3 0.000000 0.999997 -0.999997
--
q20 :: Field a => Quaternion a
q20 = quat irt2 (-irt2) 0 0

-- |
--
-- @ q21 ≡ q01 >< q20 @
--
q21 :: Field a => Quaternion a
q21 = quat 0.5 (-0.5) 0.5 0.5

-- |
--
-- @ q22 ≡ q02 >< q20 @
--
q22 :: Field a => Quaternion a
q22 =  quat 0 0 irt2 irt2

-- |
--
-- @ q23 ≡ q03 >< q20 @
--
q23 :: Field a => Quaternion a
q23 = quat 0.5 (-0.5) (-0.5) (-0.5)

-------------------------------------------------------------------------------
-- Constants
-------------------------------------------------------------------------------

-- Inverse square root of 2.
irt2 :: Field a => a
irt2 = 0.70710678118

-- Inverse square root of 3.
irt3 :: Field a => a
irt3 = 0.57735026919

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semigroup a => Semigroup (Quaternion a) where
  --(Quaternion r1 v1) <> (Quaternion r2 v2) = Quaternion (r1 <> r2) (v1 <> v2)
  (<>) = mzipWithRep (<>)

instance Monoid a => Monoid (Quaternion a) where
  mempty = pureRep mempty

instance Group a => Group (Quaternion a) where
  (<<) = mzipWithRep (<<)
  negate = fmap negate

instance Ring a => Semiring (Quaternion a) where
  fromBoolean a = Quaternion (fromBoolean a) mempty
  {-# INLINE fromBoolean #-}

  -- >>> qi >< qj :: QuatM
  -- Quaternion 0.000000 (V3 0.000000 0.000000 1.000000)
  -- >>> qk >< qi :: QuatM
  -- Quaternion 0.000000 (V3 0.000000 1.000000 0.000000)
  -- >>> qj >< qk :: QuatM
  -- Quaternion 0.000000 (V3 1.000000 0.000000 0.000000)
  Quaternion r1 v1 >< Quaternion r2 v2 = Quaternion (r1 >< r2 << (v1 <.> v2)) $ (v1 <@> v2) <> fmap (r1 ><) v2 <> fmap (r2 ><) v1
  {-# INLINE (><) #-}

instance Ring a => Ring (Quaternion a) where
  fromInteger a = Quaternion (fromInteger a) mempty

-- | (Right) division ring over /a/.
--
-- Note that, due to non-commutativity, it is possible to divide
-- in two different ways.
--
-- See < https://en.wikipedia.org/wiki/Quaternion#Unit_quaternion >.
--
-- >>> q = Quaternion 1 (V3 1 2 3) :: QuatR
-- >>> q // q
-- Quaternion (15 % 1) (V3 (0 % 1) (0 % 1) (0 % 1))
--
instance Field a => Semifield (Quaternion a) where
  fromRational a = Quaternion (fromRational a) mempty

  -- >>> qi // qj :: QuatM
  -- Quaternion 0.000000 (V3 0.000000 0.000000 -1.000000)
  -- >>> qk // qi :: QuatM
  -- Quaternion 0.000000 (V3 0.000000 -1.000000 0.000000)
  -- >>> qj // qk :: QuatM
  -- Quaternion 0.000000 (V3 -1.000000 0.000000 0.000000)
  x // y = x >< recip y
  {-# INLINE (//) #-}


  recip q = (// quadrance q) <$> conj q 
  {-# INLINE recip #-}

instance Semiring a => Semimodule a (Quaternion a) where
  a .# q = (a ><) <$> q

instance Functor Quaternion where
  fmap f (Quaternion r v) = Quaternion (f r) (fmap f v)
  {-# INLINE fmap #-}

  a <$ _ = Quaternion a (V3 a a a)
  {-# INLINE (<$) #-}

instance Foldable Quaternion where
  foldMap f (Quaternion e v) = f e <> foldMap f v
  {-# INLINE foldMap #-}
  foldr f z (Quaternion e v) = f e (foldr f z v)
  {-# INLINE foldr #-}
  null _ = False
  length _ = 4

instance Foldable1 Quaternion where
  foldMap1 f (Quaternion r v) = f r <> foldMap1 f v
  {-# INLINE foldMap1 #-}

instance Distributive Quaternion where
  distribute f = Quaternion (fmap (\(Quaternion x _) -> x) f) $ V3
    (fmap (\(Quaternion _ (V3 y _ _)) -> y) f)
    (fmap (\(Quaternion _ (V3 _ z _)) -> z) f)
    (fmap (\(Quaternion _ (V3 _ _ w)) -> w) f)
  {-# INLINE distribute #-}

instance Representable Quaternion where
  type Rep Quaternion = Maybe I3

  tabulate f = Quaternion (f Nothing) (V3 (f $ Just I31) (f $ Just I32) (f $ Just I33))
  {-# INLINE tabulate #-}

  index (Quaternion r v) = maybe r (index v)
  {-# INLINE index #-}

divq :: Semiring a => (a -> a -> a) -> (a -> a) -> Quaternion a -> Quaternion a -> Quaternion a
divq (//) negate (Quaternion q0 (V3 q1 q2 q3)) (Quaternion r0 (V3 r1 r2 r3)) = Quaternion (r0><q0 <> r1><q1 <> r2><q2 <> r3><q3) imag
  where denom = r0><r0 <> r1><r1 <> r2><r2 <> r3><r3
        imag = (V3 (r0><q1 <> (negate r1><q0) <> (negate r2><q3) <> r3><q2)
                   (r0><q2 <> r1><q3 <> (negate r2><q0) <> (negate r3><q1))
                   (r0><q3 <> (negate r1><q2) <> r2><q1 <> (negate r3><q0)))
        vec = fmap (//denom) imag
{-# INLINE divq #-}

(/) :: QuatD -> QuatD -> QuatD
(/) = divq (N./) N.negate
{-# INLINE (/) #-}

{-
tanhrhs :: QuatD -> QuatD -> QuatD -> QuatD
tanhrhs cai ai d -- = cai * (sin ai / ai) / d
  | d >= -4.2173720203427147e-29 && d < 4.446702369113811e64 = cai / (d >< (ai / sin ai))
  | otherwise                                                = cai >< (1 N./ ai N./ sin ai) N./ d
-}
