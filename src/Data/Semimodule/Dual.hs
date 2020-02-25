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


module Data.Semimodule.Dual (
  -- * Linear functionals
    Dual(..)
  , image'
  , (!*)
  , (*!)
  , toTran
  , fromTran 
  -- * Common linear functionals 
  , init
  , coinit
  , joined'
  , cojoined'
  , convolve'
) where

import safe Control.Applicative
import safe Data.Functor.Rep hiding (Co)
import safe Data.Foldable (foldl')
import safe Data.Semiring
import safe Data.Semimodule
import safe Data.Semimodule.Algebra
import safe Prelude hiding (Num(..), Fractional(..), init, negate, sum, product)
import safe Control.Monad (MonadPlus(..))

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

-- | TODO: Document
--
init :: Unital a b => b -> Dual a ()
init = fromTran initial

-- | TODO: Document
--
coinit :: Counital a c => Dual a c
coinit = Dual counital

-- | TODO: Document
--
joined' :: Algebra a b => b -> Dual a (b,b)
joined' b = Dual $ \k -> joined (curry k) b

-- | TODO: Document
--
-- @
-- 'cojoined'' = 'curry' '$' 'fromTran' 'codiagonal'
-- @
--
cojoined' :: Coalgebra a c => c -> c -> Dual a c
cojoined' x y = Dual $ \k -> cojoined k x y 

-- | TODO: Document
--
convolve' :: Algebra a b => Coalgebra a c => (b -> Dual a c) -> (b -> Dual a c) -> b -> Dual a c
convolve' f g c = do
   (c1,c2) <- joined' c
   a1 <- f c1
   a2 <- g c2
   cojoined' a1 a2

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
  (<>) = liftA2 $ \(Dual f) (Dual g) -> Dual $ \k -> f (\m -> g (cojoined k m))

instance Counital a b => Monoid (Multiplicative (Dual a b)) where
  mempty = Multiplicative $ Dual counital

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
