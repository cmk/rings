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
{-# LANGUAGE RankNTypes                 #-}

module Data.Semimodule.Algebra (
  -- * Algebras 
    type FreeAlgebra
  , Algebra(..)
  , diag
  , (.*.)
  -- * Unital algebras 
  , type FreeUnital
  , Unital(..)
  , unit
  , unit'
  -- * Coalgebras 
  , type FreeCoalgebra
  , Coalgebra(..)
  , codiag
  , convolve
  -- * Unital coalgebras 
  , type FreeCounital
  , Counital(..)
  , counit
  , inner
  -- * Bialgebras 
  , type FreeBialgebra
  , Bialgebra
  -- * Tran
  , Tran(..)
  , Endo 
  , image
  , (!#)
  , (#!)
  , (!#!)
  , dimap'
  , lmap'
  , rmap'
  , invmap
  -- * Common linear transformations
  , braid
  , cobraid 
  , split
  , cosplit
  , projl
  , projr
  , compl
  , compr
  , complr
) where

import safe Control.Arrow
import safe Control.Applicative
import safe Control.Category (Category, (>>>))
import safe Data.Bool
import safe Data.Functor.Contravariant
--import safe qualified Data.Functor.Contravariant.Rep as F
import safe Data.Functor.Rep
import safe Data.Semimodule
import safe Data.Semiring
import safe Data.Tuple (swap)
import safe Prelude (Ord, reverse)
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Set as Set
import safe qualified Data.Sequence as Seq
import safe Data.Sequence hiding (reverse,index)
import safe Prelude hiding (Num(..), Fractional(..), negate, sum, product)
import safe qualified Control.Category as C
import safe Test.Logic hiding (join)

-------------------------------------------------------------------------------
-- Algebras
-------------------------------------------------------------------------------

-- | An algebra over a free module /f/.
--
-- Note that this is distinct from a < https://en.wikipedia.org/wiki/Free_algebra free algebra >.
--
type FreeAlgebra a f = (FreeSemimodule a f, Algebra a (Rep f))

-- | An < https://en.wikipedia.org/wiki/Algebra_over_a_field#Generalization:_algebra_over_a_ring algebra > over a semiring.
--
-- Note that the algebra < https://en.wikipedia.org/wiki/Non-associative_algebra needn't be associative >.
--
class Semiring a => Algebra a b where

  -- |
  --
  -- @
  -- 'joined' = 'runTran' 'diagonal' '.' 'uncurry'
  -- @
  --
  joined :: (b -> b -> a) -> b -> a
  joined = runTran diagonal . uncurry

  -- |
  --
  -- @
  -- 'rmap'' (\((c1,()),(c2,())) -> (c1,c2)) '$' ('C.id' '***' 'initial') 'C..' 'diagonal' = 'C.id'
  -- 'rmap'' (\(((),c1),((),c2)) -> (c1,c2)) '$' ('initial' '***' 'C.id') 'C..' 'diagonal' = 'C.id'
  -- @
  --
  diagonal :: Tran a b (b,b)
  diagonal = Tran $ joined . curry

-- | Obtain a vector from a tensor.
--
-- When the algebra is trivial we have:
--
-- @ 'diag' f = 'tabulate' $ 'joined' ('index' . 'index' ('getCompose' f)) @
--
-- >>> diag $ m22 1.0 2.0 3.0 4.0
-- V2 1.0 4.0
--
diag :: FreeAlgebra a f => (f**f) a -> f a
diag f = diagonal !# f

infixl 7 .*.

-- | Multiplication operator on an algebra over a free semimodule.
--
-- /Caution/ in general (.*.) needn't be commutative, nor associative.
--
(.*.) :: FreeAlgebra a f => f a -> f a -> f a
(.*.) x y = tabulate $ joined (\i j -> index x i * index y j)

--(.#.) x y  = F.tabulate $ joined (\i j -> F.index x i * F.index y j)

-------------------------------------------------------------------------------
-- Unital algebras
-------------------------------------------------------------------------------

-- | A unital algebra over a free semimodule /f/.
--
type FreeUnital a f = (FreeAlgebra a f, Unital a (Rep f))

-- | A < https://en.wikipedia.org/wiki/Algebra_over_a_field#Unital_algebra unital algebra > over a semiring.
--
class Algebra a b => Unital a b where

  -- |
  --
  -- @
  -- 'unital' = 'runTran' 'initial' '.' 'const'
  -- @
  --
  unital :: a -> b -> a
  unital = runTran initial . const

  initial :: Tran a b ()
  initial = Tran $ \k -> unital $ k ()

-- | Insert an element into an algebra.
--
-- >>> V4 1 2 3 4 .*. unit two :: V4 Int
-- V4 2 4 6 8
--
unit :: FreeUnital a f => a -> f a
unit = tabulate . unital

-- | Unital element of a unital algebra over a free semimodule.
--
-- >>> unit' :: Complex Int
-- 1 :+ 0
--
unit' :: FreeUnital a f => f a
unit' = unit one

-------------------------------------------------------------------------------
-- Coalgebras
-------------------------------------------------------------------------------

-- | A coalgebra over a free semimodule /f/.
--
type FreeCoalgebra a f = (FreeSemimodule a f, Coalgebra a (Rep f))

-- | A coalgebra over a semiring.
--
class Semiring a => Coalgebra a c where

  -- |
  --
  -- @
  -- 'cojoined' = 'curry' '.' 'runTran' 'codiagonal'
  -- @
  --
  cojoined :: (c -> a) -> c -> c -> a
  cojoined = curry . runTran codiagonal
  
  -- |
  --
  -- @
  -- 'lmap'' (\(c1,c2) -> ((c1,()),(c2,()))) '$' ('C.id' '***' 'coinitial') 'C..' 'codiagonal' = 'C.id'
  -- 'lmap'' (\(c1,c2) -> (((),c1),((),c2))) '$' ('coinitial' '***' 'C.id') 'C..' 'codiagonal' = 'C.id'
  -- @
  --
  codiagonal :: Tran a (c,c) c
  codiagonal = Tran $ uncurry . cojoined

{-

prop_cojoined (~~) f = (codiagonal !# f) ~~ (Compose . tabulate $ \i -> tabulate $ \j -> cojoined (index f) i j)

-- trivial coalgebra
prop_codiagonal' (~~) f = (codiagonal !# f) ~~ (Compose $ flip imapRep f $ \i x -> flip imapRep f $ \j _ -> bool zero x $ (i == j))

-- trivial coalgebra
prop_codiagonal (~~) f = (codiagonal !# f) ~~ (flip bindRep id . getCompose $ f)

prop_diagonal (~~) f = (diagonal !# f) ~~ (tabulate $ joined (index . index (getCompose f)))
-}

-- | Obtain a tensor from a vector.
--
-- When the coalgebra is trivial we have:
--
-- @ 'codiag' = 'flip' 'bindRep' 'id' '.' 'getCompose' @
--
codiag :: FreeCoalgebra a f => f a -> (f**f) a
codiag f = codiagonal !# f

{-
λ> foo = convolve (tran $ m22 1 0 0 1) (tran $ m22 1 0 0 1)
λ> foo !# V2 1 2 :: V2 Int
V2 1 2
λ> foo = convolve (tran $ m22 1 0 0 1) (tran $ m22 1 1 1 1)
λ> foo !# V2 1 2 :: V2 Int
V2 1 2
λ> foo = convolve (tran $ m22 1 1 1 1) (tran $ m22 1 1 1 1)
λ> foo !# V2 1 2 :: V2 Int
V2 3 3
-}

-- | Convolution with an associative algebra and coassociative coalgebra
--
--
convolve :: Algebra a b => Coalgebra a c => Tran a b c -> Tran a b c -> Tran a b c
convolve f g = codiagonal !#! (f *** g) !#! diagonal

-------------------------------------------------------------------------------
-- Counital Coalgebras
-------------------------------------------------------------------------------

-- | A counital coalgebra over a free semimodule /f/.
--
type FreeCounital a f = (FreeCoalgebra a f, Counital a (Rep f))

-- | A counital coalgebra over a semiring.
--
class Coalgebra a c => Counital a c where

  -- @
  -- 'counital' = 'flip' ('runTran' 'coinitial') '()'
  -- @
  --
  counital :: (c -> a) -> a
  counital = flip (runTran coinitial) ()

  coinitial :: Tran a () c
  coinitial = Tran $ const . counital

-- | Obtain an element from a coalgebra over a free semimodule.
--
counit :: FreeCounital a f => f a -> a
counit = counital . index

infix 6 `inner`

-- | Inner product.
--
-- This is a variant of 'Data.Semiring.xmult' restricted to free functors.
--
-- >>> V3 1 2 3 `inner` V3 1 2 3
-- 14
-- 
inner :: FreeCounital a f => f a -> f a -> a
inner x y = counit $ liftR2 (*) x y
{-# INLINE inner #-}

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
-- General linear transformations
-------------------------------------------------------------------------------

-- | A linear transformation between free semimodules indexed with bases /b/ and /c/.
--
-- @
-- f '!#' x '+' y = (f '!#' x) + (f '!#' y)
-- f '!#' (r '.*' x) = r '.*' (f '!#' x)
-- @
--
-- /Caution/: You must ensure these laws hold when using the default constructor.
--
-- Prefer 'image' or 'Data.Semimodule.Operator.tran' where appropriate.
--
newtype Tran a b c = Tran { runTran :: (c -> a) -> b -> a }

-- | An endomorphism over a free semimodule.
--
-- >>> one + two !# V2 1 2 :: V2 Double
-- V2 3.0 6.0
--
type Endo a b = Tran a b b

-- | Create a 'Tran' from a linear combination of basis vectors.
--
-- >>> image (e2 [(2, E31),(3, E32)] [(1, E33)]) !# V3 1 1 1 :: V2 Int
-- V2 5 1
--
image :: Semiring a => (b -> [(a, c)]) -> Tran a b c
image f = Tran $ \k b -> sum [ a * k c | (a, c) <- f b ]

infixr 2 !#

-- | Apply a transformation to a vector.
--
(!#) :: Free f => Free g => Tran a (Rep f) (Rep g) -> g a -> f a
(!#) t = tabulate . runTran t . index

infixl 2 #!

-- | Apply a transformation to a vector.
--
(#!) :: Free f => Free g => g a -> Tran a (Rep f) (Rep g) -> f a
(#!) = flip (!#)

infixr 1 !#!

-- | Compose two transformations.
--
-- Provided for convenience:
--
-- @
-- ('!#!') = ('C..')
-- @
--
(!#!) :: Tran a c d -> Tran a b c -> Tran a b d
(!#!) = (C..)

-- | 'Tran' is a profunctor in the category of semimodules.
--
-- /Caution/: Arbitrary mapping functions may violate linearity.
--
-- >>> dimap' id (e3 True True False) (arr id) !# 4 :+ 5 :: V3 Int
-- V3 5 5 4
--
dimap' :: (b1 -> b2) -> (c1 -> c2) -> Tran a b2 c1 -> Tran a b1 c2
dimap' l r f = arr r !#! f !#! arr l

lmap' :: (b1 -> b2) -> Tran a b2 c -> Tran a b1 c
lmap' l = dimap' l id

rmap' :: (c1 -> c2) -> Tran a b c1 -> Tran a b c2
rmap' = dimap' id

-- | 'Tran' is an invariant functor.
--
-- See also < http://comonad.com/reader/2008/rotten-bananas/ >.
--
invmap :: (a1 -> a2) -> (a2 -> a1) -> Tran a1 b c -> Tran a2 b c
invmap f g (Tran t) = Tran $ \x -> t (x >>> g) >>> f

-------------------------------------------------------------------------------
-- Common linear transformations
-------------------------------------------------------------------------------

-- | Swap components of a tensor product.
--
-- This is equivalent to a matrix transpose.
--
braid :: Tran a (b , c) (c , b)
braid = arr swap
{-# INLINE braid #-}

-- | Swap components of a direct sum.
--
cobraid :: Tran a (b + c) (c + b)
cobraid = arr eswap
{-# INLINE cobraid #-}

-- | TODO: Document
--
split :: (b -> (b1 , b2)) -> Tran a b1 c -> Tran a b2 c -> Tran a b c
split f x y = dimap' f fst $ x *** y
{-# INLINE split #-}

-- | TODO: Document
--
cosplit :: ((c1 + c2) -> c) -> Tran a b c1 -> Tran a b c2 -> Tran a b c
cosplit f x y = dimap' Left f $ x +++ y
{-# INLINE cosplit #-}

-- | Project onto the left-hand component of a direct sum.
--
projl :: Free f => Free g => (f++g) a -> f a
projl fg = arr Left !# fg
{-# INLINE projl #-}

-- | Project onto the right-hand component of a direct sum.
--
projr :: Free f => Free g => (f++g) a -> g a
projr fg = arr Right !# fg
{-# INLINE projr #-}

-- | Left (post) composition with a linear transformation.
--
compl :: Free f1 => Free f2 => Free g => Tran a (Rep f1) (Rep f2) -> (f2**g) a -> (f1**g) a
compl t fg = first t !# fg

-- | Right (pre) composition with a linear transformation.
--
compr :: Free f => Free g1 => Free g2 => Tran a (Rep g1) (Rep g2) -> (f**g2) a -> (f**g1) a
compr t fg = second t !# fg

-- | Left and right composition with a linear transformation.
--
-- @ 'complr' f g = 'compl' f '>>>' 'compr' g @
--
complr :: Free f1 => Free f2 => Free g1 => Free g2 => Tran a (Rep f1) (Rep f2) -> Tran a (Rep g1) (Rep g2) -> (f2**g2) a -> (f1**g1) a
complr t1 t2 fg = t1 *** t2 !# fg

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semiring a => Algebra a () where
  joined f = f ()

instance Semiring a => Unital a () where
  unital r () = r

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
  coinitial = Tran $ \f _ -> f ()

instance (Coalgebra a c1, Coalgebra a c2) => Coalgebra a (c1, c2) where
  cojoined f (a1,b1) (a2,b2) = cojoined (\a -> cojoined (\b -> f (a,b)) b1 b2) a1 a2

instance (Counital a c1, Counital a c2) => Counital a (c1, c2) where
  counital k = counital $ \a -> counital $ \b -> k (a,b)

instance (Coalgebra a c1, Coalgebra a c2, Coalgebra a c3) => Coalgebra a (c1, c2, c3) where
  cojoined f (a1,b1,c1) (a2,b2,c2) = cojoined (\a -> cojoined (\b -> cojoined (\c -> f (a,b,c)) c1 c2) b1 b2) a1 a2

instance (Counital a c1, Counital a c2, Counital a c3) => Counital a (c1, c2, c3) where
  counital k = counital $ \a -> counital $ \b -> counital $ \c -> k (a,b,c)

instance Algebra a b => Coalgebra a (b -> a) where
  cojoined k f g = k (f * g)

instance Unital a b => Counital a (b -> a) where
  coinitial = Tran $ \f _ -> f one

-- | The tensor coalgebra on /c/.
--
instance Semiring a => Coalgebra a [c] where
  cojoined f as bs = f (mappend as bs)

instance Semiring a => Counital a [c] where
  coinitial = Tran $ \f _ -> f []

instance Semiring a => Coalgebra a (Seq c) where
  cojoined f as bs = f (mappend as bs)

instance Semiring a => Counital a (Seq c) where
  coinitial = Tran $ \f _ -> f Seq.empty

-- | The free commutative band coalgebra
instance (Semiring a, Ord c) => Coalgebra a (Set.Set c) where
  cojoined f as bs = f (Set.union as bs)

instance (Semiring a, Ord c) => Counital a (Set.Set c) where
  coinitial = Tran $ \f _ -> f Set.empty

-- | The free commutative band coalgebra over Int
instance Semiring a => Coalgebra a IntSet.IntSet where
  cojoined f as bs = f (IntSet.union as bs)

instance Semiring a => Counital a IntSet.IntSet where
  coinitial = Tran $ \f _ -> f IntSet.empty

{-
-- | The free commutative coalgebra over a set and a given semigroup
instance (Semiring r, Ord a, Additive b) => Coalgebra r (Map a b) where
  cojoined f as bs = f (Map.unionWith (+) as bs)
  counital k = k (Map.empty)

-- | The free commutative coalgebra over a set and Int
instance (Semiring r, Additive b) => Coalgebra r (IntMap b) where
  cojoined f as bs = f (IntMap.unionWith (+) as bs)
  counital k = k (IntMap.empty)
-}

---------------------------------------------------------------------
-- Bialgebra instances
---------------------------------------------------------------------

instance Semiring a => Bialgebra a () where
instance (Bialgebra a b1, Bialgebra a b2) => Bialgebra a (b1, b2) where
instance (Bialgebra a b1, Bialgebra a b2, Bialgebra a b3) => Bialgebra a (b1, b2, b3) where

instance Semiring a => Bialgebra a [b]
instance Semiring a => Bialgebra a (Seq b)


-------------------------------------------------------------------------------
-- Tran instances
-------------------------------------------------------------------------------

addTran :: (Additive-Semigroup) a => Tran a b c -> Tran a b c -> Tran a b c
addTran (Tran f) (Tran g) = Tran $ f + g

subTran :: (Additive-Group) a => Tran a b c -> Tran a b c -> Tran a b c
subTran (Tran f) (Tran g) = Tran $ \h -> f h - g h

-- mulTran :: (Multiplicative-Semigroup) a => Tran a b c -> Tran a b c -> Tran a b c
-- mulTran (Tran f) (Tran g) = Tran $ \h -> f h * g h

instance Functor (Tran a b) where
  fmap f m = Tran $ \k -> m !# k . f

instance Applicative (Tran a b) where
  pure a = Tran $ \k _ -> k a
  mf <*> ma = Tran $ \k b -> (mf !# \f -> (ma !# k . f) b) b

instance Monad (Tran a b) where
  return a = Tran $ \k _ -> k a
  m >>= f = Tran $ \k b -> (m !# \a -> (f a !# k) b) b

instance Category (Tran a) where
  id = Tran id
  Tran f . Tran g = Tran $ g . f

instance Arrow (Tran a) where
  arr f = Tran (. f)
  first m = Tran $ \k (a,c) -> (m !# \b -> k (b,c)) a
  second m = Tran $ \k (c,a) -> (m !# \b -> k (c,b)) a
  m *** n = Tran $ \k (a,c) -> (m !# \b -> (n !# \d -> k (b,d)) c) a
  m &&& n = Tran $ \k a -> (m !# \b -> (n !# \c -> k (b,c)) a) a

instance ArrowChoice (Tran a) where
  left m = Tran $ \k -> either (m !# k . Left) (k . Right)
  right m = Tran $ \k -> either (k . Left) (m !# k . Right)
  m +++ n =  Tran $ \k -> either (m !# k . Left) (n !# k . Right)
  m ||| n = Tran $ \k -> either (m !# k) (n !# k)

instance ArrowApply (Tran a) where
  app = Tran $ \k (f,a) -> (f !# k) a

instance (Additive-Monoid) a => ArrowZero (Tran a) where
  zeroArrow = Tran zero

instance (Additive-Monoid) a => ArrowPlus (Tran a) where
  (<+>) = addTran

instance (Additive-Semigroup) a => Semigroup (Additive (Tran a b c)) where
  (<>) = liftA2 addTran

instance (Additive-Monoid) a => Monoid (Additive (Tran a b c)) where
  mempty = pure . Tran $ const zero

instance Coalgebra a c => Semigroup (Multiplicative (Tran a b c)) where
  (<>) = liftR2 $ \ f g -> Tran $ \k b -> (f !# \a -> (g !# cojoined k a) b) b

instance Counital a c => Monoid (Multiplicative (Tran a b c)) where
  mempty = pure . Tran $ \k _ -> counital k

instance Coalgebra a c => Presemiring (Tran a b c)
instance Counital a c => Semiring (Tran a b c)

instance Counital a m => LeftSemimodule (Tran a b m) (Tran a b m) where
  lscale = (*)

instance LeftSemimodule r s => LeftSemimodule r (Tran s b m) where
  lscale s (Tran m) = Tran $ \k b -> s *. m k b

instance Counital a m => RightSemimodule (Tran a b m) (Tran a b m) where
  rscale = (*)

instance RightSemimodule r s => RightSemimodule r (Tran s b m) where
  rscale s (Tran m) = Tran $ \k b -> m k b .* s

instance (Additive-Group) a => Magma (Additive (Tran a b c)) where
  (<<) = liftR2 subTran

instance (Additive-Group) a => Quasigroup (Additive (Tran a b c)) where
instance (Additive-Group) a => Loop (Additive (Tran a b c)) where
instance (Additive-Group) a => Group (Additive (Tran a b c)) where

instance (Ring a, Counital a c) => Ring (Tran a b c)



{-

-- | An endomorphism of endomorphisms. 
--
-- @ 'Cayley' a = (a -> a) -> (a -> a) @
--
type Cayley a = Tran a a a

-- | Lift a semiring element into a 'Cayley'.
--
-- @ 'runCayley' . 'cayley' = 'id' @
--
-- >>> runCayley . cayley $ 3.4 :: Double
-- 3.4
-- >>> runCayley . cayley $ m22 1 2 3 4 :: M22 Int
-- Compose (V2 (V2 1 2) (V2 3 4))
-- 
cayley :: Semiring a => a -> Cayley a
cayley a = Tran $ \k b -> a * k zero + b

-- | Extract a semiring element from a 'Cayley'.
--
-- >>> runCayley $ two * (one + (cayley 3.4)) :: Double
-- 8.8
-- >>> runCayley $ two * (one + (cayley $ m22 1 2 3 4)) :: M22 Int
-- Compose (V2 (V2 4 4) (V2 6 10))
--
runCayley :: Semiring a => Cayley a -> a
runCayley (Tran f) = f (one +) zero

-- ring homomorphism from a -> a^b
--embed :: Counital a c => (b -> a) -> Tran a b c
embed f = Tran $ \k b -> f b * k one

-- if the characteristic of s does not divide the order of a, then s[a] is semisimple
-- and if a has a length function, we can build a filtered algebra

-- | The < https://en.wikipedia.org/wiki/Augmentation_(algebra) augmentation > ring homomorphism from a^b -> a
--
augment :: Semiring a => Tran a b c -> b -> a
augment m = m !# const one



-}



