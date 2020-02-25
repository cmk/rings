{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE RankNTypes                 #-}


module Data.Semimodule.Transform where
{- (
  -- * Types
    type (**) 
  , type (++) 
  -- * Linear functionals
  , Dual(..)
  , dual
  , image'
  , (!*)
  , (*!)
  , toTran
  , fromTran 
  -- * Linear transformations 
  , Endo 
  , Tran(..)
  , arr
  , tran
  , image 
  , (!#)
  , (#!)
  , (!#!)
  , dimap
  , invmap
  -- * Common linear transformations 
  , init
  , init'
  , coinit
  , coinit'
  , braid
  , cobraid 
  , join
  , join'
  , cojoin
  , cojoin'
  -- * Other operations
  , split
  , cosplit
  , convolve
  , convolve'
  , commutator
  -- * Matrix arithmetic
  , (.#)
  , (#.)
  , (.#.)
  , outer
  , inner
  , quadrance
  , trace
  , transpose
  -- * Matrix constructors and accessors
  , diag
  , codiag
  , scalar
  , identity
  , row
  , rows
  , col
  , cols
  , projl
  , projr
  , compl
  , compr
  , complr
  -- * Representable
  , Representable(..)
) where
-}

import safe Control.Arrow
import safe Control.Applicative
import safe Control.Category (Category, (>>>), (<<<))
import safe Data.Functor.Compose
import safe Data.Functor.Product
import safe Data.Functor.Rep hiding (Co)
import safe Data.Foldable (foldl')
import safe Data.Semiring
import safe Data.Semimodule
import safe Data.Semimodule.Algebra
import safe Data.Tuple (swap)
import safe Prelude hiding (Num(..), Fractional(..), init, negate, sum, product)
import safe Test.Logic hiding (join)
import safe qualified Control.Category as C
import safe qualified Control.Monad as M
import safe Control.Monad (MonadPlus(..))

infixr 2 **
infixr 1 ++

-- | A tensor product of semimodule morphisms.
--
type (f ** g) = Compose f g

-- | A direct sum of free semimodule elements.
--
type (f ++ g) = Product f g

-------------------------------------------------------------------------------
-- Linear functionals
-------------------------------------------------------------------------------

infixr 3 `runDual`
-- | Linear functionals from elements of a free semimodule to a scalar.
--
-- @ 
-- f '!*' (x '+' y) = (f '!*' x) '+' (f '!*' y)
-- f '!*' (x '.*' a) = a '*' (f '!*' x)
-- @
--
-- /Caution/: You must ensure these laws hold when using the default constructor.
--
newtype Dual a c = Dual { runDual :: (c -> a) -> a }

-- | Create a 'Dual' from a linear combination of basis vectors.
--
-- >>> image' [(2, E31),(3, E32)] !* V3 1 1 1 :: Int
-- 5
--
image' :: Semiring a => Foldable f => f (a, c) -> Dual a c
image' f = Dual $ \k -> foldl' (\acc (a, c) -> acc + a * k c) zero f 

-- | Obtain a linear transfrom from a linear functional.
--
toTran :: (b -> Dual a c) -> Tran a b c
toTran f = Tran $ \k b -> f b !* k

-- | Obtain a linear functional from a linear transform.
--
fromTran :: Tran a b c -> b -> Dual a c
fromTran m b = Dual $ \k -> (m !# k) b

infixr 3 !*

-- | Apply a linear functional to a vector.
--
(!*) :: Free f => Dual a (Rep f) -> f a -> a
(!*) f x = runDual f $ index x

infixl 3 *!

-- | Apply a linear functional to a vector.
--
(*!) :: Free f => f a -> Dual a (Rep f) -> a 
(*!) = flip (!*)

-------------------------------------------------------------------------------
-- General linear transformations
-------------------------------------------------------------------------------

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

infix 2 !#!

-- | Compose two transformations.
--
(!#!) :: Tran a c d -> Tran a b c -> Tran a b d
(!#!) = (C..)

-- | 'Tran' is a profunctor in the category of semimodules.
--
-- /Caution/: Arbitrary mapping functions may violate linearity.
--
-- >>> dimap id (e3 True True False) (arr id) !# 4 :+ 5 :: V3 Int
-- V3 5 5 4
--
dimap :: (b1 -> b2) -> (c1 -> c2) -> Tran a b2 c1 -> Tran a b1 c2
dimap l r f = arr r <<< f <<< arr l

-- | 'Tran' is an invariant functor.
--
-- See also < http://comonad.com/reader/2008/rotten-bananas/ >.
--
invmap :: (a1 -> a2) -> (a2 -> a1) -> Tran a1 b c -> Tran a2 b c
invmap f g (Tran t) = Tran $ \x -> t (x >>> g) >>> f

-------------------------------------------------------------------------------
-- Common linear transformations
-------------------------------------------------------------------------------

{-

prop_cojoin (~~) f = (cojoin !# f) ~~ (Compose . tabulate $ \i -> tabulate $ \j -> coappend (index f) i j)

prop_diag' (~~) f = (diag !# f) ~~ (Compose $ flip imapRep f $ \i x -> flip imapRep f $ \j _ -> bool zero x $ (i == j))

prop_diag (~~) f = (diag !# f) ~~ (flip bindRep id . getCompose $ f)

prop_codiag (~~) f = (codiag !# f) ~~ (tabulate $ append (index . index (getCompose f)))
-}

-- | Swap components of a tensor product.
--
braid :: Tran a (b , c) (c , b)
braid = arr swap
{-# INLINE braid #-}

-- | Swap components of a direct sum.
--
cobraid :: Tran a (b + c) (c + b)
cobraid = arr eswap
{-# INLINE cobraid #-}

-- | Commutator or Lie bracket of two semimodule endomorphisms.
--
commutator :: (Additive-Group) a => Endo a b -> Endo a b -> Endo a b
commutator x y = (x <<< y) - (y <<< x)

-------------------------------------------------------------------------------
-- Other operations
-------------------------------------------------------------------------------

-- | TODO: Document
--
split :: (b -> (b1 , b2)) -> Tran a b1 c -> Tran a b2 c -> Tran a b c
split f x y = dimap f fst $ x *** y
{-# INLINE split #-}

-- | TODO: Document
--
cosplit :: ((c1 + c2) -> c) -> Tran a b c1 -> Tran a b c2 -> Tran a b c
cosplit f x y = dimap Left f $ x +++ y
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
-- Dual instances
-------------------------------------------------------------------------------

instance Functor (Dual a) where
  fmap f m = Dual $ \k -> m `runDual` k . f

instance Applicative (Dual a) where
  pure a = Dual $ \k -> k a
  mf <*> ma = Dual $ \k -> mf `runDual` \f -> ma `runDual` k . f

instance Monad (Dual a) where
  return a = Dual $ \k -> k a
  m >>= f = Dual $ \k -> m `runDual` \a -> f a `runDual` k

instance (Additive-Monoid) a => Alternative (Dual a) where
  Dual m <|> Dual n = Dual $ m + n
  empty = Dual zero

instance (Additive-Monoid) a => MonadPlus (Dual a) where
  Dual m `mplus` Dual n = Dual $ m + n
  mzero = Dual zero

instance (Additive-Semigroup) a => Semigroup (Additive (Dual a b)) where
  (<>) = liftA2 $ \(Dual m) (Dual n) -> Dual $ m + n

instance (Additive-Monoid) a => Monoid (Additive (Dual a b)) where
  mempty = Additive $ Dual zero

instance Coalgebra a b => Semigroup (Multiplicative (Dual a b)) where
  (<>) = liftA2 $ \(Dual f) (Dual g) -> Dual $ \k -> f (\m -> g (coappend k m))

instance Counital a b => Monoid (Multiplicative (Dual a b)) where
  mempty = Multiplicative $ Dual coempty

instance Coalgebra a b => Presemiring (Dual a b)

instance Counital a b => Semiring (Dual a b)

instance (Additive-Group) a => Magma (Additive (Dual a b)) where
  (<<) = liftA2 $ \(Dual m) (Dual n) -> Dual $ m - n

instance (Additive-Group) a => Quasigroup (Additive (Dual a b)) where
instance (Additive-Group) a => Loop (Additive (Dual a b)) where
instance (Additive-Group) a => Group (Additive (Dual a b)) where

instance (Ring a, Counital a b) => Ring (Dual a b)

instance Counital r m => LeftSemimodule (Dual r m) (Dual r m) where
  lscale = (*)

instance LeftSemimodule r s => LeftSemimodule r (Dual s m) where
  lscale s m = Dual $ \k -> s *. runDual m k

instance Counital r m => RightSemimodule (Dual r m) (Dual r m) where
  rscale = (*)

instance RightSemimodule r s => RightSemimodule r (Dual s m) where
  rscale s m = Dual $ \k -> runDual m k .* s



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



