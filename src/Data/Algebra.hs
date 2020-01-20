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

module Data.Algebra (
    (><)
  , (//)
  , unit
  , norm
  , conj
  , reciprocal
  , Algebra(..)
  , Composition(..)
  , Unital(..)
  , Division(..)
) where

import safe Data.Magma

import safe Data.Bool
import safe Data.Complex
import safe Data.Distributive
import safe Data.Semifield
import safe Data.Fixed
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Functor.Compose
import safe Data.Functor.Rep
import safe Data.Group hiding ((//))
import safe Data.Int
import safe Data.Semiring
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Tuple
import safe Data.Word
import safe GHC.Real hiding (Fractional(..))
import safe Numeric.Natural
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe Prelude hiding (Num(..), Fractional(..), sum, product)
import safe qualified Prelude as P

import safe Data.Semigroup.Additive as A
import safe Data.Semigroup.Multiplicative as M
import safe Test.Logic

import Data.Semimodule
import Control.Applicative

-- | < https://en.wikipedia.org/wiki/Algebra_over_a_field#Generalization:_algebra_over_a_ring Algebra > over a semiring.
--
-- Needn't be associative or unital.
class Presemiring r => Algebra r a where
  multiplyWith :: (a -> a -> r) -> a -> r

infixl 7 ><

-- | Algebra product.
--
-- /Caution/ (><) needn't be commutative, nor even associative:
--
-- >>> V3 1 0 0 >< V3 0 1 0 >< V3 0 1 0 :: V3 Int
-- V3 (-1) 0 0
-- >>> V3 1 0 0 >< (V3 0 1 0 >< V3 0 1 0) :: V3 Int
-- V3 0 0 0
--
-- However the cross product does satisfy the following properties:
--
-- @ 
-- a '><' a = 'mempty'
-- a '><' b = 'negate' ( b '><' a ) , 
-- a '><' ( b <> c ) = ( a '><' b ) <> ( a '><' c ) , 
-- ( r a ) '><' b = a '><' ( r b ) = r ( a '><' b ) . 
-- a '><' ( b '><' c ) <> b '><' ( c '><' a ) <> c '><' ( a '><' b ) = 'mempty' . 
-- @
--
-- See < https://en.wikipedia.org/wiki/Jacobi_identity Jacobi identity >.
--
-- For associative algebras, use (*) instead for clarity:
--
-- >>> (1 :+ 2) >< (3 :+ 4) :: Complex Int
-- (-5) :+ 10
-- >>> (1 :+ 2) * (3 :+ 4) :: Complex Int
-- (-5) :+ 10
-- >>> qi >< qj :: QuatM
-- Quaternion 0.000000 (V3 0.000000 0.000000 1.000000)
-- >>> qi * qj :: QuatM
-- Quaternion 0.000000 (V3 0.000000 0.000000 1.000000)

(><) :: (Representable f, Algebra a (Rep f)) => f a -> f a -> f a
(><) m n = tabulate $ multiplyWith (\b1 b2 -> index m b1 * index n b2)

-- | < https://en.wikipedia.org/wiki/Composition_algebra Composition algebra > over a free semimodule.
--
class Algebra r a => Composition r a where
  conjugateWith :: (a -> r) -> a -> r

-- @ 'conj' a >< 'conj' b = 'conj' (b >< a) @
prop_conj :: Representable f => Foldable f => Semiring b => Composition a (Rep f) => Rel a b -> f a -> f a -> b
prop_conj (~~) p q = sum $ mzipWithRep (~~) (conj (p >< q)) (conj q >< conj p)

-- @ 'conj' a >< 'conj' b = 'conj' (b >< a) @
conj :: Representable f => Composition a (Rep f) => f a -> f a
conj = tabulate . conjugateWith . index

-- @ 'norm' a >< 'norm' b = 'norm' (a >< b) @
norm :: (Representable f, Composition a (Rep f)) => f a -> f a
norm x = x >< conj x

class (Semiring r, Algebra r a) => Unital r a where
  unitWith :: r -> a -> r

-- | Unit of a unital algebra.
--
-- >>> unit :: Complex Int
-- 1 :+ 0
-- >>> unit :: QuatD
-- Quaternion 1.0 (V3 0.0 0.0 0.0)
--
unit :: Representable f => Unital a (Rep f) => f a
unit = tabulate $ unitWith one

-- | A (not necessarily associative) < https://en.wikipedia.org/wiki/Division_algebra division algebra >.
--
class (Field r, Unital r a) => Division r a where
  reciprocalWith :: (a -> r) -> a -> r
  divideWith :: (a -> a -> r) -> a -> r



infixl 7 //

(//) :: Representable f => Division a (Rep f) => f a -> f a -> f a
(//) m n = tabulate $ divideWith (\b1 b2 -> index m b1 / index n b2)

--reciprocal q = (// quadrance q) <$> conj q 
reciprocal :: Representable f => Division a (Rep f) => f a -> f a
reciprocal = tabulate . reciprocalWith . index

{-
-- bilinear form induced by the composition algebra (*2)
-- (V3 1 2 3) <.> (V3 4 5 6) :: V3 Int
-- (1 :+ 2) <.> (3 :+ 4) :: Complex Double
-- quat 1 1 1 1 <.> quat 1 1 1 1 :: QuatD
--(<.>) :: Representable f => Composition a (Rep f) => Module r a => f a -> f a -> a
--(<.>) :: Representable f => Composition a (Rep f) => Group (f a) => Field a => f a -> f a -> f a
--x <.> y = (recip A.two *) <$> (norm (x <> y) << norm x << norm y)

--(<.>) :: Representable f => Composition a (Rep f) => Group (f a) => Field a => f a -> f a -> a
--x <.> y = recip two * prod where prod = flip index mempty (norm (x <> y) << norm x << norm y)

-- bar (m22 1 2 3 4) (m22 1 2 3 4)
bar
  :: (Algebra a (Rep f), Foldable1 g, Eq (Rep g),
      Representable f, Representable g
     ) =>
     f (g a) -> f (g a) -> f a
bar m n = tabulate $ multiplyWith (\b1 b2 -> index m b1 .*. index n b2)
-}




{-

-- https://en.wikipedia.org/wiki/Dual_number
Semiring k => Algebra k DualBasis
Semiring k => Algebra k ComplexBasis
outer' :: Semiring a => Functor f => Functor g => f a -> g a -> f (g a)
outer' a b = fmap (\x->fmap (><x) b) a

-- | `fromNatural` default definition
--fromNaturalRep :: (Unital r (Rep m), Representable m, Semiring r) => Natural -> m r
fromNaturalRep :: (Representable f, Unital a (Rep f), Dioid a) => Natural -> f a
fromNaturalRep n = tabulate $ unital (fromNatural n)

-- | `fromInteger` default definition
--fromIntegerRep :: (Unital r (Rep m), Representable m, Ring r) => Integer -> m r
fromIntegerRep :: (Representable f, Unital a (Rep f), Ring a) => Integer -> f a
fromIntegerRep n = tabulate $ unital (fromInteger n)
-}


---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------


--instance (Semiring r, Unital r a) => Unital r (a -> r) where
--  unitWith = unitWith one

--instance (Semiring r, Division r a) => Division r (a -> r) where
--  reciprocalWith = reciprocalWith

-- incoherent
-- instance Unital () a where unitWith _ _ = ()
-- instance (Unital r a, Unital r b) => Unital (a -> r) b where unitWith f b a = unitWith (f a) b

instance Semiring r => Algebra r () where
  multiplyWith f = f ()

instance Semiring r => Unital r () where
  unitWith r () = r

instance (Algebra r a, Algebra r b) => Algebra r (a,b) where
  multiplyWith f (a,b) = multiplyWith (\a1 a2 -> multiplyWith (\b1 b2 -> f (a1,b1) (a2,b2)) b) a

instance (Algebra r a, Algebra r b, Algebra r c) => Algebra r (a,b,c) where
  multiplyWith f (a,b,c) = multiplyWith (\a1 a2 -> multiplyWith (\b1 b2 -> multiplyWith (\c1 c2 -> f (a1,b1,c1) (a2,b2,c2)) c) b) a

instance (Unital r a, Unital r b) => Unital r (a,b) where
  unitWith r (a,b) = unitWith r a * unitWith r b

instance (Unital r a, Unital r b, Unital r c) => Unital r (a,b,c) where
  unitWith r (a,b,c) = unitWith r a * unitWith r b * unitWith r c

-- | Tensor algebra
--
-- >>> multiplyWith (<>) [1..3 :: Int]
-- [1,2,3,1,2,3,1,2,3,1,2,3]
--
-- >>> multiplyWith (\f g -> fold (f ++ g)) [1..3] :: Int
-- 24
--
instance Semiring r => Algebra r [a] where
  multiplyWith f = go [] where
    go ls rrs@(r:rs) = f (reverse ls) rrs + go (r:ls) rs
    go ls [] = f (reverse ls) []

instance Semiring r => Unital r [a] where
  unitWith r [] = r
  unitWith _ _ = zero

type ComplexBasis = Bool

-- Complex basis
--instance Module r ComplexBasis => Algebra r ComplexBasis where
instance Ring r => Algebra r ComplexBasis where
  multiplyWith f = f' where
    fe = f False False - f True True
    fi = f False True + f True False
    f' False = fe
    f' True = fi

--instance Module r ComplexBasis => Composition r ComplexBasis where
instance Ring r => Composition r ComplexBasis where
  conjugateWith f = f' where
    afe = f False
    nfi = negate (f True)
    f' False = afe
    f' True = nfi

--instance Module r ComplexBasis => Unital r ComplexBasis where
instance Ring r => Unital r ComplexBasis where
  unitWith x False = x
  unitWith _ _ = zero





