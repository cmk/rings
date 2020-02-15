{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
--{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE RankNTypes               #-}

{-# LANGUAGE DataKinds               #-}

module Data.Algebra.Quaternion where

import safe Data.Algebra
import safe Data.Algebra.Dual
import safe Data.Algebra.Split
import safe Data.Distributive
import safe Data.Fixed hiding (E2,E3,E6)
import safe Data.Functor.Classes
import safe Data.Functor.Compose
import safe Data.Functor.Rep
import safe Data.Semifield
import safe Data.Semigroup.Foldable
import safe Data.Semimodule hiding (Basis)
import safe Data.Semimodule.Free
import safe Data.Semimodule.Basis
import safe Data.Semimodule.Transform
import safe Data.Semiring
import safe GHC.Generics hiding (Rep, C, D, S)
import safe Prelude hiding (Num(..), Fractional(..), Real, sum, product)

import Data.Functor.Product
import Data.Complex

{- need tolerances:
λ> prop_conj q12 (q3 :: QuatP)
False
λ> prop_conj q14 (q3 :: QuatP)
False

prop_conj :: Ring a => (a -> a -> Bool) -> Quat a -> Quat a -> Bool
prop_conj (~~) p q = sum $ mzipWithRep (~~) (conj (p * q)) (conj q * conj p)

-- conj (p * q) = conj q * conj p
-- conj q = (-0.5) * (q <> (i * q * i) <> (j * q * j) <> (k * q * k))
-- 2 * real q '==' q <> conj q
-- 2 * imag q '==' q << conj q
conj :: Group a => Quat a -> Quat a
conj (Quat r v) = Quat r $ fmap negate v

-- TODO: add to Property module
prop_conj' :: Field a => Rel (Quat a) b -> Quat a -> b
prop_conj' (~~) q = (conj q) ~~ (conj' q) where
  conj' q = ((one / negate two) *) <$> q <> (qi * q * qi) <> (qj * q * qj) <> (qk * q * qk)


-- | < https://en.wikipedia.org/wiki/Bicomplex_number >
-- type Bicomplex r = Product C C r
type Bicomplex r = (C++C) r

-- | < https://en.wikipedia.org/wiki/Biquaternion >
--type Biquat r = Compose H C r -- == M22 (C r)

-- | < https://en.wikipedia.org/wiki/Dual_quaternion >
type DualBiquat r = (H**D) r

-- | < https://en.wikipedia.org/wiki/Split-biquaternion >
type SplitBiquat r = (H**S) r



type H = Quat

{-
traverse print $ chk dqk
chk q = fmap (q .*.) base
base = [dqu, dqi, dqj, dqk, dqe, dqei, dqej, dqek]
-}
dqu  = dquat 1.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 :: (H**D) Double
dqe  = dquat 0.0 1.0 0.0 0.0 0.0 0.0 0.0 0.0 :: DualBiquat Double
dqi  = dquat 0.0 0.0 1.0 0.0 0.0 0.0 0.0 0.0 :: DualBiquat Double
dqei = dquat 0.0 0.0 0.0 1.0 0.0 0.0 0.0 0.0 :: DualBiquat Double
dqj  = dquat 0.0 0.0 0.0 0.0 1.0 0.0 0.0 0.0 :: DualBiquat Double
dqej = dquat 0.0 0.0 0.0 0.0 0.0 1.0 0.0 0.0 :: DualBiquat Double
dqk  = dquat 0.0 0.0 0.0 0.0 0.0 0.0 1.0 0.0 :: DualBiquat Double
dqek = dquat 0.0 0.0 0.0 0.0 0.0 0.0 0.0 1.0 :: DualBiquat Double

-- | Obtain a dual quaternion from 8 real numbers.
--
dquat :: a -> a -> a -> a -> a -> a -> a -> a -> Compose H Dual a
dquat a b c d e f g h = Compose $ quat (Dual a b) (Dual c d) (Dual e f) (Dual g h)


-}






type QuatF = Quat Float
type QuatD = Quat Double
type QuatR = Quat Rational
type QuatM = Quat Micro
type QuatN = Quat Nano
type QuatP = Quat Pico

data Quat a = Quat !a {-# UNPACK #-}! (V3 a) deriving (Eq, Ord, Show, Generic, Generic1)

instance Show1 Quat where
  liftShowsPrec f g d (Quat a b) = showsBinaryWith f (liftShowsPrec f g) "H" d a b

-- | Obtain a 'Quat' from 4 base elements.
--
quat :: a -> a -> a -> a -> Quat a
quat r x y z = Quat r (V3 x y z)

-- | Real or scalar part of a quaternion.
--
scal :: Quat a -> a
scal (Quat r _) = r

vect :: Quat a -> V3 a
vect (Quat _ v) = v

-- | Use a quaternion to rotate a vector.
--
-- >>> rotate qk . rotate qj $ V3 1 1 0 :: V3 Int
-- V3 1 (-1) 0
--
rotate :: Real a => Quat a -> V3 a -> V3 a
rotate q v = v' where Quat _ v' = q * Quat zero v * conj q

-- | Scale a 'QuatD' to unit length.
--
-- >>> normalize $ normalize $ quat 2.0 2.0 2.0 2.0
-- Quat 0.5 (V3 0.5 0.5 0.5)
--
normalize :: QuatD -> QuatD
normalize q = recip (sqrt $ norm q) *. q


instance Field a => Clifford a Quat where
  quad (Quat r v) = r * r - dot v v

-------------------------------------------------------------------------------
-- Standard quaternion basis elements
-------------------------------------------------------------------------------


-- | The real quaternion.
--
-- Represents no rotation.
--
-- 'qu' = 'unit'
--
qu :: Semiring a => Quat a
qu = idx Nothing

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
-- >>> qi * qj
-- Quat 0 (V3 0 0 1)
--
qi :: Semiring a => Quat a
qi = idx (Just E31)

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
-- >>> qj * qk
-- Quat 0 (V3 1 0 0)
--
qj :: Semiring a => Quat a
qj = idx (Just E32)

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
-- >>> qk * qi
-- Quat 0 (V3 0 1 0)
-- >>> qi * qj * qk
-- Quat (-1) (V3 0 0 0)
--
qk :: Semiring a => Quat a
qk = idx (Just E33)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance (Additive-Semigroup) a => Semigroup (Quat a) where
  (<>) = mzipWithRep (+) 

instance (Additive-Monoid) a => Monoid (Quat a) where
  mempty = pureRep zero

instance (Additive-Group) a => Magma (Quat a) where
  (<<) = mzipWithRep (-)

instance (Additive-Group) a => Quasigroup (Quat a)

instance (Additive-Group) a => Loop (Quat a)

instance (Additive-Group) a => Group (Quat a)

instance (Additive-Group) a => Magma (Additive (Quat a)) where
  (<<) = mzipWithRep (<<)

instance (Additive-Group) a => Quasigroup (Additive (Quat a))

instance (Additive-Group) a => Loop (Additive (Quat a))

instance (Additive-Group) a => Group (Additive (Quat a))

instance Semiring a => LeftSemimodule a (Quat a) where
  lscale = lscaleDef
  {-# INLINE lscale #-}

instance Semiring a => RightSemimodule a (Quat a) where
  rscale = rscaleDef
  {-# INLINE rscale #-}

instance Semiring a => Bisemimodule a a (Quat a)

instance Field a => Composition a Quat where
  conj (Quat r v) = Quat r $ fmap negate v

instance Field a => Division a Quat where
  recipa f = (recip $ norm f) *. conj f

{-
reciprocal'' x = divq unit x

divq (Quaternion r0 (V3 r1 r2 r3)) (Quaternion q0 (V3 q1 q2 q3)) =
 (/denom) <$> Quaternion (r0*q0 + r1*q1 + r2*q2 + r3*q3) imag
  where denom = q0*q0 + q1*q1 + q2*q2 + q3*q3
        imag = (V3 (r0*q1 + (negate r1*q0) + (negate r2*q3) + r3*q2)
                   (r0*q2 + r1*q3 + (negate r2*q0) + (negate r3*q1))
                   (r0*q3 + (negate r1*q2) + r2*q1 + (negate r3*q0)))

-}
instance (Additive-Semigroup) a => Semigroup (Additive (Quat a)) where
  (<>) = mzipWithRep (<>)

instance (Additive-Monoid) a => Monoid (Additive (Quat a)) where
  mempty = pure mempty

instance Real a => Semigroup (Multiplicative (Quat a)) where
  -- >>> qi * qj :: QuatM
  -- Quat 0.000000 (V3 0.000000 0.000000 1.000000)
  -- >>> qk * qi :: QuatM
  -- Quat 0.000000 (V3 0.000000 1.000000 0.000000)
  -- >>> qj * qk :: QuatM
  -- Quat 0.000000 (V3 1.000000 0.000000 0.000000)
  (<>) = mzipWithRep (.*.)

instance Real a => Monoid (Multiplicative (Quat a)) where
  mempty = pure unitf

instance Real a => Presemiring (Quat a)

instance Real a => Semiring (Quat a)

instance Real a => Ring (Quat a)

instance Functor Quat where
  fmap f (Quat r v) = Quat (f r) (fmap f v)
  {-# INLINE fmap #-}

  a <$ _ = Quat a (V3 a a a)
  {-# INLINE (<$) #-}

instance Foldable Quat where
  foldMap f (Quat e v) = f e <> foldMap f v
  {-# INLINE foldMap #-}
  foldr f z (Quat e v) = f e (foldr f z v)
  {-# INLINE foldr #-}
  null _ = False
  length _ = 4

instance Foldable1 Quat where
  foldMap1 f (Quat r v) = f r <> foldMap1 f v
  {-# INLINE foldMap1 #-}

instance Distributive Quat where
  distribute f = Quat (fmap (\(Quat x _) -> x) f) $ V3
    (fmap (\(Quat _ (V3 y _ _)) -> y) f)
    (fmap (\(Quat _ (V3 _ z _)) -> z) f)
    (fmap (\(Quat _ (V3 _ _ w)) -> w) f)
  {-# INLINE distribute #-}

instance Representable Quat where
  type Rep Quat = Maybe E3

  tabulate f = Quat (f Nothing) (V3 (f $ Just E31) (f $ Just E32) (f $ Just E33))
  {-# INLINE tabulate #-}

  index (Quat r v) = maybe r (index v)
  {-# INLINE index #-}
