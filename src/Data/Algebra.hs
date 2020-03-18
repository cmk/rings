{-# LANGUAGE CPP                        #-}
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

module Data.Algebra (
  -- * Algebras 
    Algebra(..)
  -- * Unital algebras 
  , Unital(..)
  -- * Coalgebras 
  , Coalgebra(..)
  -- * Unital coalgebras 
  , Counital(..)
  -- * Bialgebras 
  , Bialgebra
) where

import Control.Applicative
import Control.Arrow
import Control.Category (Category, (<<<), (>>>))
import Data.Bool
import Data.Complex
import Data.Finite (Finite, finites)
import Data.Fixed
import Data.Functor.Apply
import Data.Functor.Compose
import Data.Functor.Contravariant
import Data.Functor.Product
import Data.Functor.Rep
import Data.Functor.Rep
import Data.Group
import Data.Int
import Data.Semiring
import Data.Sequence hiding (reverse,index)
import Data.Tuple (swap)
import Data.Word
import Foreign.C.Types (CFloat(..),CDouble(..))
import GHC.Real hiding (Fractional(..))
import GHC.TypeNats (KnownNat(..))
import Numeric.Natural
import Prelude (Ord, reverse)
import Prelude (fromInteger)
import Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import qualified Control.Category as C
import qualified Control.Monad as M
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

-------------------------------------------------------------------------------
-- Algebras
-------------------------------------------------------------------------------

-- | An < https://en.wikipedia.org/wiki/Algebra_over_a_field#Generalization:_algebra_over_a_ring algebra > over a semiring.
--
-- Note that the algebra < https://en.wikipedia.org/wiki/Non-associative_algebra needn't be associative >.
--
class Semiring a => Algebra a b where

  -- |
  --
  -- @
  -- 'joined' = 'Data.Semiring.Free.vmap' 'Data.Semiring.Free.diagonal' '.' 'uncurry'
  -- @
  --
  joined :: (b -> b -> a) -> b -> a


-- | A < https://en.wikipedia.org/wiki/Algebra_over_a_field#Unital_algebra unital algebra > over a semiring.
--
class Algebra a b => Unital a b where

  -- |
  --
  -- @
  -- 'unital' = 'Data.Semiring.Free.vmap' 'Data.Semiring.Free.initial' '.' 'const'
  -- @
  --
  unital :: a -> b -> a

-------------------------------------------------------------------------------
-- Coalgebras
-------------------------------------------------------------------------------


-- | A coalgebra over a semiring.
--
class Semiring a => Coalgebra a c where

  -- |
  --
  -- @
  -- 'cojoined' = 'curry' '.' 'Data.Semiring.Free.vmap' 'Data.Semiring.Free.codiagonal'
  -- @
  --
  cojoined :: (c -> a) -> c -> c -> a
  

-- | A counital coalgebra over a semiring.
--
class Coalgebra a c => Counital a c where

  -- @
  -- 'Data.Semiring.Free.Cov' 'counital' = 'Data.Semiring.Free.cmap' 'Data.Semiring.Free.coinitial' $ pure '()'
  -- @
  --
  counital :: (c -> a) -> a

-------------------------------------------------------------------------------
-- Bialgebras
-------------------------------------------------------------------------------

-- | A < https://en.wikipedia.org/wiki/Bialgebra bialgebra > over a semiring.
--
class (Unital a b, Counital a b) => Bialgebra a b

-------------------------------------------------------------------------------
-- Algebra instances
-------------------------------------------------------------------------------

instance Semiring a => Algebra a () where
  joined f = f ()

instance Semiring a => Unital a () where
  unital r () = r

instance Semiring a => Algebra a (Finite n) where
  joined = M.join

instance Semiring a => Unital a (Finite n) where
  unital = const

instance (Algebra a b1, Algebra a b2) => Algebra a (b1, b2) where
  joined f (a,b) = joined (\a1 a2 -> joined (\b1 b2 -> f (a1,b1) (a2,b2)) b) a

instance (Unital a b1, Unital a b2) => Unital a (b1, b2) where
  unital r (a,b) = unital r a * unital r b

instance (Algebra a b1, Algebra a b2, Algebra a b3) => Algebra a (b1, b2, b3) where
  joined f (a,b,c) = joined (\a1 a2 -> joined (\b1 b2 -> joined (\c1 c2 -> f (a1,b1,c1) (a2,b2,c2)) c) b) a

instance (Unital a b1, Unital a b2, Unital a b3) => Unital a (b1, b2, b3) where
  unital r (a,b,c) = unital r a * unital r b * unital r c

-- | Tensor algebra on /b/.
--
-- >>> joined (<>) [1..3 :: Int]
-- [1,2,3,1,2,3,1,2,3,1,2,3]
--
-- >>> joined (\f g -> fold (f ++ g)) [1..3] :: Int
-- 24
--
instance Semiring a => Algebra a [b] where
  joined f = go [] where
    go ls rrs@(r:rs) = f (reverse ls) rrs + go (r:ls) rs
    go ls [] = f (reverse ls) []

instance Semiring a => Unital a [b] where
  unital a [] = a
  unital _ _ = zero

instance Semiring a => Algebra a (Seq b) where
  joined f = go Seq.empty where
    go ls s = case viewl s of
       EmptyL -> f ls s 
       r :< rs -> f ls s + go (ls |> r) rs

instance Semiring a => Unital a (Seq b) where
  unital a b | Seq.null b = a
             | otherwise = zero

instance (Semiring a, Ord b) => Algebra a (Set.Set b) where
  joined f = go Set.empty where
    go ls s = case Set.minView s of
       Nothing -> f ls s
       Just (r, rs) -> f ls s + go (Set.insert r ls) rs

instance (Semiring a, Ord b) => Unital a (Set.Set b) where
  unital a b | Set.null b = a
           | otherwise = zero

instance Semiring a => Algebra a IntSet.IntSet where
  joined f = go IntSet.empty where
    go ls s = case IntSet.minView s of
       Nothing -> f ls s
       Just (r, rs) -> f ls s + go (IntSet.insert r ls) rs

instance Semiring a => Unital a IntSet.IntSet where
  unital a b | IntSet.null b = a
             | otherwise = zero

---------------------------------------------------------------------
-- Coalgebra instances
---------------------------------------------------------------------

instance Semiring a => Coalgebra a () where
  cojoined = const

instance Semiring a => Counital a () where
  counital f = f ()

instance Semiring a => Coalgebra a (Finite n) where
  cojoined f i j = bool zero (f i) $ i == j

instance (KnownNat n, Semiring a) => Counital a (Finite n) where
  counital f = sum . fmap f $ finites

instance Algebra a b => Coalgebra a (b -> a) where
  cojoined k f g = k (f * g)

instance Unital a b => Counital a (b -> a) where
  counital f = f one

instance (Coalgebra a c1, Coalgebra a c2) => Coalgebra a (c1, c2) where
  cojoined f (a1,b1) (a2,b2) = cojoined (\a -> cojoined (\b -> f (a,b)) b1 b2) a1 a2

instance (Counital a c1, Counital a c2) => Counital a (c1, c2) where
  counital k = counital $ \a -> counital $ \b -> k (a,b)

instance (Coalgebra a c1, Coalgebra a c2, Coalgebra a c3) => Coalgebra a (c1, c2, c3) where
  cojoined f (a1,b1,c1) (a2,b2,c2) = cojoined (\a -> cojoined (\b -> cojoined (\c -> f (a,b,c)) c1 c2) b1 b2) a1 a2

instance (Counital a c1, Counital a c2, Counital a c3) => Counital a (c1, c2, c3) where
  counital k = counital $ \a -> counital $ \b -> counital $ \c -> k (a,b,c)

-- | The tensor coalgebra on /c/.
--
instance Semiring a => Coalgebra a [c] where
  cojoined f as bs = f (mappend as bs)

instance Semiring a => Counital a [c] where
  counital f = f []

instance Semiring a => Coalgebra a (Seq c) where
  cojoined f as bs = f (mappend as bs)

instance Semiring a => Counital a (Seq c) where
  counital f = f Seq.empty

-- | The free commutative band coalgebra
instance (Semiring a, Ord c) => Coalgebra a (Set.Set c) where
  cojoined f as bs = f (Set.union as bs)

instance (Semiring a, Ord c) => Counital a (Set.Set c) where
  counital f = f Set.empty

-- | The free commutative band coalgebra over Int
instance Semiring a => Coalgebra a IntSet.IntSet where
  cojoined f as bs = f (IntSet.union as bs)

instance Semiring a => Counital a IntSet.IntSet where
  counital f = f IntSet.empty

-- | The free commutative coalgebra over a set and a given semigroup
instance (Semiring r, Ord a, Semigroup b) => Coalgebra r (Map.Map a b) where
  cojoined f as bs = f (Map.unionWith (<>) as bs)

instance (Semiring r, Ord a, Semigroup b) => Counital r (Map.Map a b) where
  counital f = f Map.empty

---------------------------------------------------------------------
-- Bialgebra instances
---------------------------------------------------------------------

instance Semiring a => Bialgebra a () where

instance (KnownNat n, Semiring a) => Bialgebra a (Finite n) where

instance (Bialgebra a b1, Bialgebra a b2) => Bialgebra a (b1, b2) where

instance (Bialgebra a b1, Bialgebra a b2, Bialgebra a b3) => Bialgebra a (b1, b2, b3) where

instance Semiring a => Bialgebra a [b]

instance Semiring a => Bialgebra a (Seq b)
