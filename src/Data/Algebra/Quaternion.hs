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

-- | See the /spatial-math/ package for usage.
module Data.Algebra.Quaternion where

import safe Data.Algebra
import safe Data.Distributive
import safe Data.Semifield
import safe Data.Functor.Rep
import safe Data.Fixed

import safe Data.Semimodule
import safe Data.Semimodule.Vector
import safe Data.Semimodule.Matrix
import safe Data.Semimodule.Transform
import safe Data.Semiring
import safe Data.Semigroup.Foldable
import safe Data.Semigroup.Additive
import safe Data.Semigroup.Multiplicative
import safe GHC.Generics hiding (Rep)

import safe Prelude (fromInteger, fromRational)
import Prelude hiding (Num(..), Fractional(..), sum, product)
import safe qualified Prelude as N

import safe Test.Logic

import GHC.Real hiding (Fractional(..))

{- need tolerances:
λ> prop_conj q12 (q3 :: QuatP)
False
λ> prop_conj q14 (q3 :: QuatP)
False

prop_conj :: Ring a => (a -> a -> Bool) -> Quaternion a -> Quaternion a -> Bool
prop_conj (~~) p q = sum $ mzipWithRep (~~) (conj (p * q)) (conj q * conj p)

-- conj (p * q) = conj q * conj p
-- conj q = (-0.5) * (q <> (i * q * i) <> (j * q * j) <> (k * q * k))
-- 2 * real q '==' q <> conj q
-- 2 * imag q '==' q << conj q
conj :: Group a => Quaternion a -> Quaternion a
conj (Quaternion r v) = Quaternion r $ fmap negate v

-- TODO: add to Property module
prop_conj' :: Field a => Rel (Quaternion a) b -> Quaternion a -> b
prop_conj' (~~) q = (conj q) ~~ (conj' q) where
  conj' q = ((one / negate two) *) <$> q <> (qi * q * qi) <> (qj * q * qj) <> (qk * q * qk)
-}





type QuatF = Quaternion Float
type QuatD = Quaternion Double
type QuatR = Quaternion Rational
type QuatM = Quaternion Micro
type QuatN = Quaternion Nano
type QuatP = Quaternion Pico

data Quaternion a = Quaternion !a {-# UNPACK #-}! (V3 a) deriving (Eq, Ord, Show, Generic, Generic1)

-- | Obtain a 'Quaternion' from 4 base field elements.
--
quat :: a -> a -> a -> a -> Quaternion a
quat r x y z = Quaternion r (V3 x y z)

-- | Real or scalar part of a quaternion.
--
scal :: Quaternion a -> a
scal (Quaternion r _) = r

vect :: Quaternion a -> V3 a
vect (Quaternion _ v) = v

-- | Use a quaternion to rotate a vector.
--
-- >>> rotate qk . rotate qj $ V3 1 1 0 :: V3 Int
-- V3 1 (-1) 0
--
rotate :: Ring a => Quaternion a -> V3 a -> V3 a
rotate q v = v' where Quaternion _ v' = q * Quaternion zero v * conj q

-- | Scale a 'QuatD' to unit length.
--
-- >>> normalize $ normalize $ quat 2.0 2.0 2.0 2.0
-- Quaternion 0.5 (V3 0.5 0.5 0.5)
--
normalize :: QuatD -> QuatD
normalize q = 1.0 / (sqrt $ norm q) *. q

-------------------------------------------------------------------------------
-- Standard quaternion basis elements
-------------------------------------------------------------------------------

-- | The real quaternion.
--
-- Represents no rotation.
--
-- 'qe' = 'unit'
--
qe :: Semiring a => Quaternion a
qe = idx Nothing

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
-- Quaternion 0 (V3 0 0 1)
--
qi :: Semiring a => Quaternion a
qi = idx (Just I31)

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
-- Quaternion 0 (V3 1 0 0)
--
qj :: Semiring a => Quaternion a
qj = idx (Just I32)

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
-- Quaternion 0 (V3 0 1 0)
-- >>> qi * qj * qk
-- Quaternion (-1) (V3 0 0 0)
--
qk :: Semiring a => Quaternion a
qk = idx (Just I33)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance (Additive-Semigroup) a => Semigroup (Quaternion a) where
  (<>) = mzipWithRep (+) 

instance (Additive-Monoid) a => Monoid (Quaternion a) where
  mempty = pureRep zero

instance (Additive-Group) a => Magma (Quaternion a) where
  (<<) = mzipWithRep (-)

instance (Additive-Group) a => Quasigroup (Quaternion a)

instance (Additive-Group) a => Loop (Quaternion a)

instance (Additive-Group) a => Group (Quaternion a)

instance (Additive-Group) a => Magma (Additive (Quaternion a)) where
  (<<) = mzipWithRep (<<)

instance (Additive-Group) a => Quasigroup (Additive (Quaternion a))

instance (Additive-Group) a => Loop (Additive (Quaternion a))

instance (Additive-Group) a => Group (Additive (Quaternion a))

instance Semiring a => Semimodule a (Quaternion a) where
  (*.) = multl

instance (Additive-Semigroup) a => Semigroup (Additive (Quaternion a)) where
  (<>) = mzipWithRep (<>)

instance (Additive-Monoid) a => Monoid (Additive (Quaternion a)) where
  mempty = pure mempty

instance Ring a => Semigroup (Multiplicative (Quaternion a)) where
  -- >>> qi * qj :: QuatM
  -- Quaternion 0.000000 (V3 0.000000 0.000000 1.000000)
  -- >>> qk * qi :: QuatM
  -- Quaternion 0.000000 (V3 0.000000 1.000000 0.000000)
  -- >>> qj * qk :: QuatM
  -- Quaternion 0.000000 (V3 1.000000 0.000000 0.000000)
  (<>) = mzipWithRep (><)

instance Ring a => Monoid (Multiplicative (Quaternion a)) where
  mempty = pure unit

instance Ring a => Presemiring (Quaternion a)

instance Ring a => Semiring (Quaternion a)

instance Ring a => Ring (Quaternion a)

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
