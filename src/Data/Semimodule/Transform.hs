{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
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
{-# LANGUAGE RankNTypes                 #-}


module Data.Semimodule.Transform (
  -- * Types
    type (**) 
  , type (++) 
  , type Dim
  , type Endo
  , Tran(..)
  , app
  , arr
  , invmap
  -- * Matrix combinators
  , rows
  , cols
  , projl
  , projr
  , compl
  , compr
  , complr
  , transpose
  -- * Dimensional combinators
  , braid
  , sbraid
  , first
  , second
  , left
  , right
  , (***)
  , (+++)
  , (&&&)
  , (|||)
  , adivide
  , aselect
) where

import safe Control.Category (Category, (>>>))
import safe Data.Functor.Compose
import safe Data.Functor.Product
import safe Data.Functor.Rep
import safe Data.Profunctor
import safe Data.Semimodule
import safe Data.Tuple (swap)
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import safe Test.Logic
import safe qualified Control.Category as C
import safe qualified Data.Bifunctor as B

infixr 2 **
infixr 1 ++

type (f ** g) = Compose f g
type (f ++ g) = Product f g

-- | A dimensional (binary) relation between two bases.
--
-- @ 'Dim' b c @ relations correspond to (compositions of) 
-- permutation, projection, and embedding transformations.
--
-- See also < https://en.wikipedia.org/wiki/Logical_matrix >.
--
type Dim b c = forall a . Tran a b c

-- | An endomorphism over a free semimodule.
--
type Endo a b = Tran a b b

-- | A morphism between free semimodules indexed with bases /b/ and /c/.
--
newtype Tran a b c = Tran { runTran :: (c -> a) -> (b -> a) } deriving Functor

instance Category (Tran a) where
  id = Tran id
  Tran f . Tran g = Tran $ g . f

instance Profunctor (Tran a) where
  lmap f (Tran t) = Tran $ \ca -> t ca . f
  rmap = fmap

---------------------------------------------------------------------

-- | Apply a transformation to a vector.
--
app :: Basis2 b c f g => Tran a b c -> g a -> f a
app t = tabulate . runTran t . index

-- | Lift a function on basis indices into a transformation.
--
-- @ 'arr' f = 'rmap' f 'C.id' @
--
arr :: (b -> c) -> Tran a b c
arr f = Tran (. f)

-- | /Tran a b c/ is an invariant functor on /a/.
--
-- See also < http://comonad.com/reader/2008/rotten-bananas/ >.
--
invmap :: (a1 -> a2) -> (a2 -> a1) -> Tran a1 b c -> Tran a2 b c
invmap f g (Tran t) = Tran $ \x -> t (x >>> g) >>> f

---------------------------------------------------------------------

-- | Obtain a matrix by stacking rows.
--
-- >>> rows (V2 1 2) :: M22 Int
-- V2 (V2 1 2) (V2 1 2)
--
rows :: Basis2 b c f g => g a -> (f**g) a
rows = app $ arr snd
{-# INLINE rows #-}

-- | Obtain a matrix by stacking columns.
--
-- >>> cols (V2 1 2) :: M22 Int
-- V2 (V2 1 1) (V2 2 2)
--
cols :: Basis2 b c f g => f a -> (f**g) a
cols = app $ arr fst
{-# INLINE cols #-}

-- | Project onto the left-hand component of a direct sum.
--
projl :: Basis2 b c f g => (f++g) a -> f a
projl = app $ arr Left
{-# INLINE projl #-}

-- | Project onto the right-hand component of a direct sum.
--
projr :: Basis2 b c f g => (f++g) a -> g a
projr = app $ arr Right
{-# INLINE projr #-}

-- | Left (post) composition with a linear transformation.
--
compl :: Basis3 b c d f1 f2 g => Dim b c -> (f2**g) a -> (f1**g) a
compl f = app (first f)

-- | Right (pre) composition with a linear transformation.
--
compr :: Basis3 b c d f g1 g2 => Dim c d -> (f**g2) a -> (f**g1) a
compr f = app (second f)

-- | Left and right composition with a linear transformation.
--
-- @ 'complr' f g = 'compl' f '>>>' 'compr' g @
--
-- When /f . g = id/ this induces a similarity transformation:
--
-- >>> perm1 = arr (+ E32)
-- >>> perm2 = arr (+ E33)
-- >>> m = m33 1 2 3 4 5 6 7 8 9 :: M33 Int
-- >>> complr perm1 perm2 m :: M33 Int
-- V3 (V3 5 6 4) (V3 8 9 7) (V3 2 3 1)
--
-- See also < https://en.wikipedia.org/wiki/Matrix_similarity > & < https://en.wikipedia.org/wiki/Conjugacy_class >.
--
complr :: Basis2 b1 c1 f1 f2 => Basis2 b2 c2 g1 g2 => Dim b1 c1 -> Dim b2 c2 -> (f2**g2) a -> (f1**g1) a
complr f g = app (f *** g)

-- | Transpose a matrix.
--
-- >>> transpose (V3 (V2 1 2) (V2 3 4) (V2 5 6))
-- V2 (V3 1 3 5) (V3 2 4 6)
--
-- >>> transpose $ m23 1 2 3 4 5 6 :: M32 Int
-- V3 (V2 1 4) (V2 2 5) (V2 3 6)
--
transpose :: Basis2 b c f g => (f**g) a -> (g**f) a
transpose = app braid
{-# INLINE transpose #-}

---------------------------------------------------------------------

-- | Swap components of a tensor product.
--
braid :: Dim (a , b) (b , a)
braid = arr swap
{-# INLINE braid #-}

-- | Swap components of a direct sum.
--
sbraid :: Dim (a + b) (b + a)
sbraid = arr eswap
{-# INLINE sbraid #-}

-- | Lift a transform into a transform on tensor products.
--
first :: Dim b c -> Dim (b , d) (c , d)
first (Tran caba) = Tran $ \cda -> cda . B.first (caba id)

-- | Lift a transform into a transform on tensor products.
--
second :: Dim b c -> Dim (d , b) (d , c)
second (Tran caba) = Tran $ \cda -> cda . B.second (caba id)

-- | Lift a transform into a transform on direct sums.
--
left :: Dim b c -> Dim (b + d) (c + d)
left (Tran caba) = Tran $ \cda -> cda . B.first (caba id)

-- | Lift a transform into a transform on direct sums.
--
right :: Dim b c -> Dim (d + b) (d + c)
right (Tran caba) = Tran $ \cda -> cda . B.second (caba id)

infixr 3 ***

-- | Create a transform on a tensor product of semimodules.
--
(***) :: Dim a1 b1 -> Dim a2 b2 -> Dim (a1 , a2) (b1 , b2)
x *** y = first x >>> arr swap >>> first y >>> arr swap
{-# INLINE (***) #-}

infixr 2 +++

-- | Create a transform on a direct sum of semimodules.
--
(+++) :: Dim a1 b1 -> Dim a2 b2 -> Dim (a1 + a2) (b1 + b2)
x +++ y = left x >>> arr eswap >>> left y >>> arr eswap
{-# INLINE (+++) #-}

infixr 3 &&&

-- | Create a transform on a tensor product of semimodules.
--
(&&&) :: Dim a b1 -> Dim a b2 -> Dim a (b1 , b2)
x &&& y = dimap fork id $ x *** y
{-# INLINE (&&&) #-}

infixr 2 |||

-- | Create a transform on a direct sum of semimodules.
--
(|||) :: Dim a1 b -> Dim a2 b -> Dim (a1 + a2) b
x ||| y = dimap id join $ x +++ y
{-# INLINE (|||) #-}

-- |
--
-- @ 'adivide' 'fork' = 'C.id' @ 
--
adivide :: (a -> (a1 , a2)) -> Dim a1 b -> Dim a2 b -> Dim a b
adivide f x y = dimap f fst $ x *** y
{-# INLINE adivide #-}

-- |
--
-- @ 'aselect' 'join' = 'C.id' @ 
--
aselect :: ((b1 + b2) -> b) -> Dim a b1 -> Dim a b2 -> Dim a b
aselect f x y = dimap Left f $ x +++ y
{-# INLINE aselect #-}
