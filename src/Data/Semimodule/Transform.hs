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


module Data.Semimodule.Transform where

import safe Control.Category (Category, (>>>))
import safe Data.Functor.Compose
import safe Data.Functor.Product
import safe Data.Functor.Rep
import safe Data.Profunctor
import safe Data.Semiring
import safe Data.Semimodule
import safe Data.Tuple (swap)
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import safe Test.Logic
import safe qualified Control.Category as C
import safe qualified Data.Bifunctor as B

{-
app' = app @E3 @V3 @E3 @V3 @Int

-- >>> app' foo $ V3 1 2 3
-- V3 2 1 3
-- >>> app' foo >>> app' foo $ V3 1 2 3
-- V3 1 2 3
-- >>> app' (foo >>> foo) $ V3 1 2 3
-- V3 1 2 3
--
foo = Tran $ \f -> f . t
 where
  t E31 = E32
  t E32 = E31
  t E33 = E33

-}

infixr 2 **
infixr 1 ++

type (f ** g) = Compose f g
type (f ++ g) = Product f g

---------------------------------------------------------------------

-- | A binary relation between two basis indices.
--
-- @ 'Index' b c @ relations correspond to (compositions of) 
-- permutation, projection, and embedding transformations.
--
-- See also < https://en.wikipedia.org/wiki/Logical_matrix >.
--
type Index b c = forall a . Tran a b c

-- | A general transformation between free semimodules indexed with bases /b/ and /c/.
--
newtype Tran a b c = Tran { runTran :: (c -> a) -> (b -> a) } deriving Functor

app :: Basis b f => Basis c g => Tran a b c -> g a -> f a
app t = tabulate . runTran t . index

instance Category (Tran a) where
  id = Tran id
  Tran f . Tran g = Tran $ g . f

instance Profunctor (Tran a) where
  lmap f (Tran t) = Tran $ \ca -> t ca . f
  rmap = fmap

-- | /Tran a b c/ is an invariant functor on /a/.
--
-- See also < http://comonad.com/reader/2008/rotten-bananas/ >.
--
invmap :: (a1 -> a2) -> (a2 -> a1) -> Tran a1 b c -> Tran a2 b c
invmap f g (Tran t) = Tran $ \x -> t (x >>> g) >>> f

---------------------------------------------------------------------

-- | An endomorphism over a free semimodule.
--
type Endo a b = Tran a b b

-- | Obtain a matrix by stacking rows.
--
-- >>> rows (V2 1 2) :: M22 Int
-- V2 (V2 1 2) (V2 1 2)
--
rows :: Free f => Free g => g a -> f (g a)
rows = getCompose . app in1 
{-# INLINE rows #-}

-- | Obtain a matrix by stacking columns.
--
-- >>> cols (V2 1 2) :: M22 Int
-- V2 (V2 1 1) (V2 2 2)
--
cols :: Free f => Free g => f a -> f (g a)
cols = getCompose . app in2
{-# INLINE cols #-}

projl :: Free f => Free g => Product f g a -> f a
projl = app exl

projr :: Free f => Free g => Product f g a -> g a
projr = app exr

-- | Left (post) composition with a linear transformation.
--
compl :: Bases b c f1 f2 => Free g => Index b c -> f2 (g a) -> f1 (g a)
compl f = getCompose . app (first f) . Compose

-- | Right (pre) composition with a linear transformation.
--
compr :: Bases b c g1 g2 => Free f => Index b c -> f (g2 a) -> f (g1 a)
compr f = getCompose . app (second f) . Compose

-- | Left and right composition with a linear transformation.
--
-- @ 'complr f g' = 'compl f' . 'compr g' @
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
complr :: Bases b1 c1 f1 f2 => Bases b2 c2 g1 g2 => Index b1 c1 -> Index b2 c2 -> f2 (g2 a) -> f1 (g1 a)
complr f g =  getCompose . app (f *** g) . Compose

-- | Transpose a matrix.
--
-- >>> transpose (V3 (V2 1 2) (V2 3 4) (V2 5 6))
-- V2 (V3 1 3 5) (V3 2 4 6)
--
-- >>> transpose $ m23 1 2 3 4 5 6 :: M32 Int
-- V3 (V2 1 4) (V2 2 5) (V2 3 6)
--
transpose :: Free f => Free g => f (g a) -> g (f a)
transpose = getCompose . app braid . Compose
{-# INLINE transpose #-}

---------------------------------------------------------------------

-- arr toE3 :: Dim3 e => Index e E3

-- @ 'arr' f = 'rmap' f 'C.id' @
arr :: (b -> c) -> Index b c
arr f = Tran (. f)

in1 :: Index (a , b) b
in1 = arr snd
{-# INLINE in1 #-}

in2 :: Index (a , b) a
in2 = arr fst
{-# INLINE in2 #-}

exl :: Index a (a + b)
exl = arr Left
{-# INLINE exl #-}

exr :: Index b (a + b)
exr = arr Right
{-# INLINE exr #-}

braid :: Index (a , b) (b , a)
braid = arr swap
{-# INLINE braid #-}

ebraid :: Index (a + b) (b + a)
ebraid = arr eswap
{-# INLINE ebraid #-}

first :: Index b c -> Index (b , d) (c , d)
first (Tran caba) = Tran $ \cda -> cda . B.first (caba id)

second :: Index b c -> Index (d , b) (d , c)
second (Tran caba) = Tran $ \cda -> cda . B.second (caba id)

left :: Index b c -> Index (b + d) (c + d)
left (Tran caba) = Tran $ \cda -> cda . B.first (caba id)

right :: Index b c -> Index (d + b) (d + c)
right (Tran caba) = Tran $ \cda -> cda . B.second (caba id)

infixr 3 ***

(***) :: Index a1 b1 -> Index a2 b2 -> Index (a1 , a2) (b1 , b2)
x *** y = first x >>> arr swap >>> first y >>> arr swap
{-# INLINE (***) #-}

infixr 2 +++

(+++) :: Index a1 b1 -> Index a2 b2 -> Index (a1 + a2) (b1 + b2)
x +++ y = left x >>> arr eswap >>> left y >>> arr eswap
{-# INLINE (+++) #-}

infixr 3 &&&

(&&&) :: Index a b1 -> Index a b2 -> Index a (b1 , b2)
x &&& y = dimap fork id $ x *** y
{-# INLINE (&&&) #-}

infixr 2 |||

(|||) :: Index a1 b -> Index a2 b -> Index (a1 + a2) b
x ||| y = dimap id join $ x +++ y
{-# INLINE (|||) #-}

infixr 0 $$$

($$$) :: Index a (b -> c) -> Index a b -> Index a c
($$$) f x = dimap fork apply (f *** x)
{-# INLINE ($$$) #-}

adivide :: (a -> (a1 , a2)) -> Index a1 b -> Index a2 b -> Index a b
adivide f x y = dimap f fst $ x *** y
{-# INLINE adivide #-}

adivide' :: Index a b -> Index a b -> Index a b
adivide' = adivide fork
{-# INLINE adivide' #-}

adivided :: Index a1 b -> Index a2 b -> Index (a1 , a2) b
adivided = adivide id
{-# INLINE adivided #-}

aselect :: ((b1 + b2) -> b) -> Index a b1 -> Index a b2 -> Index a b
aselect f x y = dimap Left f $ x +++ y
{-# INLINE aselect #-}

aselect' :: Index a b -> Index a b -> Index a b
aselect' = aselect join
{-# INLINE aselect' #-}

aselected :: Index a b1 -> Index a b2 -> Index a (b1 + b2)
aselected = aselect id
{-# INLINE aselected #-}



