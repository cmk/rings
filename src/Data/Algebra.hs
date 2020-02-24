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

module Data.Algebra (
  -- * Algebras 
    type FreeAlgebra
  , Algebra(..)
  , (.*.)
  -- * Unital Algebras 
  , type FreeUnital
  , Unital(..)
  , unital
  , unit
  -- * Coalgebras 
  , type FreeCoalgebra
  , Coalgebra(..)
  -- * Unital Coalgebras 
  , type FreeCounital
  , Counital(..)
  , counital
  -- * Bialgebras 
  , type FreeBialgebra
  , Bialgebra
) where

import safe Data.Bool
import safe Data.Functor.Rep
import safe Data.Semimodule
import safe Data.Semiring
import safe Prelude (Ord, reverse)
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Set as Set
import safe qualified Data.Sequence as Seq
import safe Data.Sequence hiding (reverse,index)
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)

-------------------------------------------------------------------------------
-- Algebras
-------------------------------------------------------------------------------

-- | An algebra over a free module /f/.
--
-- Note that this is distinct from a < https://en.wikipedia.org/wiki/Free_algebra free algebra >.
--
type FreeAlgebra a f = (FreeSemimodule a f, Algebra a (Rep f))

-- | An algebra < https://en.wikipedia.org/wiki/Algebra_over_a_field#Generalization:_algebra_over_a_ring algebra > over a semiring.
--
-- Note that the algebra < https://en.wikipedia.org/wiki/Non-associative_algebra needn't be associative >.
--
class Semiring a => Algebra a b where
  append :: (b -> b -> a) -> b -> a

infixl 7 .*.

-- | Multiplication operator on an algebra over a free semimodule.
--
-- /Caution/ in general (.*.) needn't be commutative, nor associative.
--
(.*.) :: FreeAlgebra a f => f a -> f a -> f a
(.*.) x y = tabulate $ append (\i j -> index x i * index y j)

-------------------------------------------------------------------------------
-- Unital algebras
-------------------------------------------------------------------------------

-- | A unital algebra over a free semimodule /f/.
--
type FreeUnital a f = (FreeAlgebra a f, Unital a (Rep f))

-- | A < https://en.wikipedia.org/wiki/Algebra_over_a_field#Unital_algebra unital algebra > over a semiring.
--
class Algebra a b => Unital a b where
  aempty :: a -> b -> a

-- | Insert an element into an algebra.
--
-- >>> V4 1 2 3 4 .*. unital two :: V4 Int
-- V4 2 4 6 8
unital :: FreeUnital a f => a -> f a
unital = tabulate . aempty

-- | Unital element of a unital algebra over a free semimodule.
--
-- >>> unit :: Complex Int
-- 1 :+ 0
-- >>> unit :: QuatD
-- Quaternion 1.0 (V3 0.0 0.0 0.0)
--
unit :: FreeUnital a f => f a
unit = unital one

-------------------------------------------------------------------------------
-- Coalgebras
-------------------------------------------------------------------------------

-- | A coalgebra over a free semimodule /f/.
--
type FreeCoalgebra a f = (FreeSemimodule a f, Coalgebra a (Rep f))

-- | A coalgebra over a semiring.
--
class Semiring a => Coalgebra a c where
  -- ( id *** coempty ) . coappend = id = ( coempty *** id ) . coappend
  coappend :: (c -> a) -> c -> c -> a

-------------------------------------------------------------------------------
-- Counital Coalgebras
-------------------------------------------------------------------------------

-- | A counital coalgebra over a free semimodule /f/.
--
type FreeCounital a f = (FreeCoalgebra a f, Counital a (Rep f))

-- | A counital coalgebra over a semiring.
--
class Coalgebra a c => Counital a c where
  coempty :: (c -> a) -> a

-- | Obtain an element from a coalgebra over a free semimodule.
--
counital :: FreeCounital a f => f a -> a
counital = coempty . index

-------------------------------------------------------------------------------
-- Bialgebras
-------------------------------------------------------------------------------

-- | A bialgebra over a free semimodule /f/.
--
type FreeBialgebra a f = (FreeAlgebra a f, FreeCoalgebra a f, Bialgebra a (Rep f))

-- | A < https://en.wikipedia.org/wiki/Bialgebra bialgebra > over a semiring.
--
class (Unital a b, Counital a b) => Bialgebra a b

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------


instance Semiring a => Algebra a () where
  append f = f ()

instance Semiring a => Unital a () where
  aempty r () = r

instance (Algebra a b1, Algebra a b2) => Algebra a (b1, b2) where
  append f (a,b) = append (\a1 a2 -> append (\b1 b2 -> f (a1,b1) (a2,b2)) b) a

instance (Unital a b1, Unital a b2) => Unital a (b1, b2) where
  aempty r (a,b) = aempty r a * aempty r b

instance (Algebra a b1, Algebra a b2, Algebra a b3) => Algebra a (b1, b2, b3) where
  append f (a,b,c) = append (\a1 a2 -> append (\b1 b2 -> append (\c1 c2 -> f (a1,b1,c1) (a2,b2,c2)) c) b) a

instance (Unital a b1, Unital a b2, Unital a b3) => Unital a (b1, b2, b3) where
  aempty r (a,b,c) = aempty r a * aempty r b * aempty r c

-- | Tensor algebra on /b/.
--
-- >>> append (<>) [1..3 :: Int]
-- [1,2,3,1,2,3,1,2,3,1,2,3]
--
-- >>> append (\f g -> fold (f ++ g)) [1..3] :: Int
-- 24
--
instance Semiring a => Algebra a [b] where
  append f = go [] where
    go ls rrs@(r:rs) = f (reverse ls) rrs + go (r:ls) rs
    go ls [] = f (reverse ls) []

instance Semiring a => Unital a [b] where
  aempty a [] = a
  aempty _ _ = zero

instance Semiring a => Algebra a (Seq b) where
  append f = go Seq.empty where
    go ls s = case viewl s of
       EmptyL -> f ls s 
       r :< rs -> f ls s + go (ls |> r) rs

instance Semiring a => Unital a (Seq b) where
  aempty a b | Seq.null b = a
             | otherwise = zero

instance (Semiring a, Ord b) => Algebra a (Set.Set b) where
  append f = go Set.empty where
    go ls s = case Set.minView s of
       Nothing -> f ls s
       Just (r, rs) -> f ls s + go (Set.insert r ls) rs

instance (Semiring a, Ord b) => Unital a (Set.Set b) where
  aempty a b | Set.null b = a
           | otherwise = zero

instance Semiring a => Algebra a IntSet.IntSet where
  append f = go IntSet.empty where
    go ls s = case IntSet.minView s of
       Nothing -> f ls s
       Just (r, rs) -> f ls s + go (IntSet.insert r ls) rs

instance Semiring a => Unital a IntSet.IntSet where
  aempty a b | IntSet.null b = a
             | otherwise = zero

---------------------------------------------------------------------
-- Coalgebra instances
---------------------------------------------------------------------


instance Semiring a => Coalgebra a () where
  coappend = const

instance Semiring a => Counital a () where
  coempty f = f ()

instance (Coalgebra a c1, Coalgebra a c2) => Coalgebra a (c1, c2) where
  coappend f (a1,b1) (a2,b2) = coappend (\a -> coappend (\b -> f (a,b)) b1 b2) a1 a2

instance (Counital a c1, Counital a c2) => Counital a (c1, c2) where
  coempty k = coempty $ \a -> coempty $ \b -> k (a,b)

instance (Coalgebra a c1, Coalgebra a c2, Coalgebra a c3) => Coalgebra a (c1, c2, c3) where
  coappend f (a1,b1,c1) (a2,b2,c2) = coappend (\a -> coappend (\b -> coappend (\c -> f (a,b,c)) c1 c2) b1 b2) a1 a2

instance (Counital a c1, Counital a c2, Counital a c3) => Counital a (c1, c2, c3) where
  coempty k = coempty $ \a -> coempty $ \b -> coempty $ \c -> k (a,b,c)

instance Algebra a b => Coalgebra a (b -> a) where
  coappend k f g = k (f * g)

instance Unital a b => Counital a (b -> a) where
  coempty k = k one

-- | The tensor coalgebra on /c/.
--
instance Semiring a => Coalgebra a [c] where
  coappend f as bs = f (mappend as bs)

instance Semiring a => Counital a [c] where
  coempty k = k []

instance Semiring a => Coalgebra a (Seq c) where
  coappend f as bs = f (mappend as bs)

instance Semiring a => Counital a (Seq c) where
  coempty k = k (Seq.empty)

-- | The free commutative band coalgebra
instance (Semiring a, Ord c) => Coalgebra a (Set.Set c) where
  coappend f as bs = f (Set.union as bs)

instance (Semiring a, Ord c) => Counital a (Set.Set c) where
  coempty k = k (Set.empty)

-- | The free commutative band coalgebra over Int
instance Semiring a => Coalgebra a IntSet.IntSet where
  coappend f as bs = f (IntSet.union as bs)

instance Semiring a => Counital a IntSet.IntSet where
  coempty k = k (IntSet.empty)

{-
-- | The free commutative coalgebra over a set and a given semigroup
instance (Semiring r, Ord a, Additive b) => Coalgebra r (Map a b) where
  coappend f as bs = f (Map.unionWith (+) as bs)
  coempty k = k (Map.empty)

-- | The free commutative coalgebra over a set and Int
instance (Semiring r, Additive b) => Coalgebra r (IntMap b) where
  coappend f as bs = f (IntMap.unionWith (+) as bs)
  coempty k = k (IntMap.empty)
-}

---------------------------------------------------------------------
-- Bialgebra instances
---------------------------------------------------------------------

instance Semiring a => Bialgebra a () where
instance (Bialgebra a b1, Bialgebra a b2) => Bialgebra a (b1, b2) where
instance (Bialgebra a b1, Bialgebra a b2, Bialgebra a b3) => Bialgebra a (b1, b2, b3) where

instance Semiring a => Bialgebra a [b]
instance Semiring a => Bialgebra a (Seq b)
