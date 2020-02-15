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

module Data.Algebra where
{- (
    type FreeAlgebra
  , Algebra(..)
  , type FreeComposition
  , Composition(..)
  , type FreeUnital
  , Unital(..)
  , type FreeDivision
  , Division(..)
  , (.*.)
  , (//)
  , (.@.)
  , unit
  , norm
  , conj
  , triple
  , reciprocal

) where
-}

import safe Control.Category ((>>>))
import safe Data.Bool
import safe Data.Complex
import safe Data.Functor.Rep
import safe Data.Semifield
import safe Data.Semigroup.Additive as A
import safe Data.Semigroup.Multiplicative as M
import safe Data.Semimodule
import safe Data.Semiring hiding ((//))
import safe Prelude hiding (Num(..), Fractional(..), Real, sum, product)
import Data.Functor.Classes

import safe qualified Data.IntSet as IntSet
import safe qualified Data.Set as Set


import qualified Data.Sequence as Seq
import Data.Sequence hiding (reverse,index)


-- | An algebra over a free semimodule.
--type FreeAlgebra a f = (FreeSemimodule a f, Algebra a (Rep f))
type FreeAlgebra a f = (Free f, Algebra a (Rep f))

-- | A unital algebra over a free semimodule.
type FreeUnital a f = (FreeAlgebra a f, Unital a (Rep f))


-- | < https://en.wikipedia.org/wiki/Algebra_over_a_field#Generalization:_algebra_over_a_ring Algebra > over a semiring.
--
-- Needn't be associative or unital.
--
class Semiring a => Algebra a b where
  mult :: (b -> b -> a) -> b -> a


infixl 7 .*.

-- | Multiplication operator on a free algebra.
--
-- In particular this is cross product on the standard basis in /R^3/:
--
-- >>> V3 1 0 0 .*. V3 0 1 0 .*. V3 0 1 0 :: V3 Int
-- V3 (-1) 0 0
-- >>> V3 1 0 0 .*. (V3 0 1 0 .*. V3 0 1 0) :: V3 Int
-- V3 0 0 0
--
-- For Lie algebras like one above, '.*.' satisfies the following properties:
--
-- @ 
-- a '.*.' a = 'mempty'
-- a '.*.' b = 'negate' ( b '.*.' a ) , 
-- a '.*.' ( b <> c ) = ( a '.*.' b ) <> ( a '.*.' c ) , 
-- ( r a ) '.*.' b = a '.*.' ( r b ) = r ( a '.*.' b ) . 
-- a '.*.' ( b '.*.' c ) <> b '.*.' ( c '.*.' a ) <> c '.*.' ( a '.*.' b ) = 'mempty' . 
-- @
--
-- See < https://en.wikipedia.org/wiki/Jacobi_identity Jacobi identity >.
--
-- /Caution/ in general (.*.) needn't be commutative, nor even associative.
--
-- For associative algebras, consider implementing `Multiplicative``-``Semigroup` as well for clarity:
--
-- >>> (1 :+ 2) .*. (3 :+ 4) :: Complex Int
-- (-5) :+ 10
-- >>> (1 :+ 2) * (3 :+ 4) :: Complex Int
-- (-5) :+ 10
-- >>> qi .*. qj :: QuatM
-- Quaternion 0.000000 (V3 0.000000 0.000000 1.000000)
-- >>> qi * qj :: QuatM
-- Quaternion 0.000000 (V3 0.000000 0.000000 1.000000)
--
(.*.) :: FreeAlgebra a f => f a -> f a -> f a
(.*.) x y = tabulate $ mult (\i j -> index x i * index y j)



class (Semiring a, Algebra a b) => Unital a b where
  unit :: a -> b -> a

-- | Unital element of a free unital algebra.
--
-- >>> aunit :: Complex Int
-- 1 :+ 0
-- >>> aunit :: QuatD
-- Quaternion 1.0 (V3 0.0 0.0 0.0)
--
unitf :: FreeUnital a f => f a
unitf = tabulate $ unit one


-- | A (not necessarily associative) < https://en.wikipedia.org/wiki/Division_algebra division algebra >.
--
class (Semifield a, FreeUnital a f) => Division a f where
  
  -- | Reciprocal operator.
  --
  -- When /f/ is a composition algebra we must have:
  --
  -- @ 'recipa' x = ('recip' $ 'norm' f) '*.' 'conj' f
  --
  -- See 'Data.Algebra.Property'.
  --
  recipa :: f a -> f a
  recipa f = unitf ./. f

  infixl 7 ./.
  -- | Division operator.
  --
  -- >>> (1 :+ 0) ./. (0 :+ 1)
  -- 0.0 :+ (-1.0)
  -- >>> qe ./. qi :: QuatD
  -- Quat 0.0 (V3 (-1.0) 0.0 0.0)
  --
  (./.) :: f a -> f a -> f a
  (./.) x y = x .*. recipa y

  infixl 7 .\.
  -- | Left division operator.
  --
  -- >>> (1 :+ 0) .\. (0 :+ 1)
  -- 0.0 :+ 1.0
  -- >>> qe .\. qi :: QuatD
  -- Quat 0.0 (V3 1.0 0.0 0.0)
  --
  (.\.) :: f a -> f a -> f a
  (.\.) x y = recipa x .*. y


-- | A < https://en.wikipedia.org/wiki/Composition_algebra composition algebra >.
--
class Clifford a f => Composition a f where

  -- | Conjugation operator.
  --
  -- @ 'conj' a '.*.' 'conj' b = 'conj' (b .*. a) @
  --
  conj :: f a -> f a

  -- | Norm operator on a free composition algebra.
  --
  -- @ 
  -- 'norm' x '*' 'norm' y = 'norm' (x .*. y)
  -- 'norm' x '*' 'norm' x = 'norm' $ x .*. 'conj' x
  -- @
  --
  norm :: f a -> a
  norm = quad
  --default norm :: (Rep f) ~ Maybe e => f a -> a
  --norm f = flip index Nothing $ f .*. conj f


-- | Bilinear form on a free composition algebra.
--
-- 
-- See 'Data.Algebra.Property'.
--
-- >>> V2 1 2 .@. V2 1 2
-- 5.0
-- >>> V2 1 2 .@. V2 2 (-1)
-- 0.0
-- >>> V3 1 1 1 .@. V3 1 1 (-2)
-- 0.0
-- 
-- >>> (1 :+ 2) .@. (2 :+ (-1)) :: Double
-- 0.0
--
-- >>> qi .@. qj :: Double
-- 0.0
-- >>> qj .@. qk :: Double
-- 0.0
-- >>> qk .@. qi :: Double
-- 0.0
-- >>> qk .@. qk :: Double
-- 1.0
--
--foldcomp :: Composition a f => f a -> f a -> a
--foldcomp = symmetric norm

symmetric :: Field a => (Additive-Semigroup) b => (b -> a) -> b -> b -> a
symmetric q x y = prod / two where prod = q (x + y) - q x - q y


-- | Interior product
-- prop_cliff x y = x .*. y + y .*. x = (two * x .@. y) *. unitf
(.@.) :: Clifford a f => FreeModule a f => f a -> f a -> f a
x .@. y = ((recip two) *) <$> x .*. y + y .*. x

-- | Exterior product
--
(.^.) :: Clifford a f => FreeModule a f => f a -> f a -> f a
x .^. y = ((recip two) *) <$> x .*. y - y .*. x

c x y = x :+ y :: Complex Double
{-
x = c 1 2
y = c 3 4

traverse print $ chk dqk
chk q = fmap (q .*.) base
base = [dqu, dqi, dqj, dqk, dqe, dqei, dqej, dqek]


-}
foo x y = x .*. y + y .*. x 
bar x y = (two * x .@. y) *. unitf

--prop_cliff x y = x .*. y + y .*. x == (two * x .@. y) *. unitf

prop_cliff x = x .*. x == quad x *. unitf

class (Field a, FreeUnital a f) => Clifford a f where
  -- | 
  --
  -- @
  -- x '.*.' x = 'quad' x '*.' 'unitf'
  -- x .*. y + y .*. x = (two * x .@. y) *. unitf
  -- x .*. y = x .@. y + x .^. y
  -- @
  quad :: f a -> a

{-
https://en.wikipedia.org/wiki/Multivector
class (Field a, Unital a b) => Clifford a b where
  quad :: (b -> a) -> a
-}

{-

instance Clifford C where
instance Clifford (C++C) where
-}

type C2 = Bool

instance Ring r => Algebra r C2 where
  mult f False = f False False - f True True
  mult f True = f False True + f True False

instance Ring r => Unital r C2 where
  unit x False = x
  unit _ _ = zero

instance Real a => Clifford a Complex where
  quad (x :+ y) = flip index False $ (x :+ y) * (x :+ (-y))

instance Real a => Composition a Complex where
  conj (x :+ y) = x :+ negate y

instance Real a => Division a Complex where
  recipa f = (recip $ norm f) *. conj f

{-

instance Ring r => Algebra r ComplexBasis where

  mult f False = f False False + f True True
  mult f True = f False True - f True False

instance Field a => Clifford a Complex where
  quad = norm --(x :+ y) = x * x - y * y
  (a1 :+ a2) .@. (b1 :+ b2) = (a1*b1 + a2*b2) :+ (a1*b2 - a2*b1)



--instance Module r ComplexBasis => Composition r ComplexBasis where
instance Ring r => Composition r ComplexBasis where
  conjugateWith f = f' where
    afe = f False
    nfi = negate (f True)
    f' False = afe
    f' True = nfi

  normWith f = flip multiplyWith zero $ \e1 e2 -> f e1 * conjugateWith f e2

--instance Module r ComplexBasis => Unital r ComplexBasis where



-- Complex basis
--instance Module a ComplexBasis => Algebra a ComplexBasis where
instance Ring a => Algebra a ComplexBasis where
  mult f = f' where
    fe = f False False - f True True
    fi = f False True + f True False
    f' False = fe
    f' True = fi

instance Ring a => Unital a ComplexBasis where
  unit x False = x
  unit _ _ = zero



-}

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------


--instance (Semiring a, Unital a b) => Unital a (a -> r) where
--  unit = unit one

--instance (Semiring a, Division a b) => Division r (a -> r) where
--  reciprocalWith = reciprocalWith

-- incoherent
-- instance Unital () a where unit _ _ = ()
-- instance (Unital a b, Unital a c) => Unital (a -> r) b where unit f b a = unit (f a) b
--instance (Unital r a, Unital r b) => Unital (a -> r) b where unit f b a = unit (f a) b

--instance (Algebra r b, Algebra r a) => Algebra (b -> r) a where mult f a b = mult (\a1 a2 -> f a1 a2 b) a


instance Semiring a => Algebra a () where
  mult f = f ()

instance (Algebra a b, Algebra a c) => Algebra a (b, c) where
  mult f (a,b) = mult (\a1 a2 -> mult (\b1 b2 -> f (a1,b1) (a2,b2)) b) a

instance (Algebra a b, Algebra a c, Algebra a d) => Algebra a (b, c, d) where
  mult f (a,b,c) = mult (\a1 a2 -> mult (\b1 b2 -> mult (\c1 c2 -> f (a1,b1,c1) (a2,b2,c2)) c) b) a

instance Semiring a => Unital a () where
  unit r () = r

instance (Unital a b, Unital a c) => Unital a (b, c) where
  unit r (a,b) = unit r a * unit r b

instance (Unital a b, Unital a c, Unital a d) => Unital a (b, c, d) where
  unit r (a,b,c) = unit r a * unit r b * unit r c

-- | Tensor algebra
--
-- >>> mult (<>) [1..3 :: Int]
-- [1,2,3,1,2,3,1,2,3,1,2,3]
--
-- >>> mult (\f g -> fold (f ++ g)) [1..3] :: Int
-- 24
--
instance Semiring a => Algebra a [a] where
  mult f = go [] where
    go ls rrs@(r:rs) = f (reverse ls) rrs + go (r:ls) rs
    go ls [] = f (reverse ls) []

-- | The tensor algebra
instance Semiring r => Algebra r (Seq a) where
  mult f = go Seq.empty where
    go ls s = case viewl s of
       EmptyL -> f ls s 
       r :< rs -> f ls s + go (ls |> r) rs

instance (Semiring r) => Unital r (Seq a) where
  unit r a | Seq.null a = r
           | otherwise = zero

instance (Semiring r, Ord a) => Algebra r (Set.Set a) where
  mult f = go Set.empty where
    go ls s = case Set.minView s of
       Nothing -> f ls s
       Just (r, rs) -> f ls s + go (Set.insert r ls) rs

instance Semiring r => Algebra r IntSet.IntSet where
  mult f = go IntSet.empty where
    go ls s = case IntSet.minView s of
       Nothing -> f ls s
       Just (r, rs) -> f ls s + go (IntSet.insert r ls) rs

instance Semiring a => Unital a [a] where
  unit a [] = a
  unit _ _ = zero

instance (Semiring r, Ord a) => Unital r (Set.Set a) where
  unit r a | Set.null a = r
           | otherwise = zero

instance Semiring r => Unital r IntSet.IntSet where
  unit r a | IntSet.null a = r
           | otherwise = zero



