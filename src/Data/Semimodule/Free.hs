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


module Data.Semimodule.Free (
  -- * Types
    type Free
  , type Base
  , Op(..)
  , (!*)
  , (*!)
  , toTran
  , fromTran
  -- * Vectors
  , type Vec
  , runVec
  , vec
  , vmap
  , join
  , init
  -- * Covectors
  , Cov(..)
  , cov
  , cmap
  , cojoin
  , coinit
  , images
) where

import safe Control.Applicative
import safe Data.Functor.Rep
import safe Data.Functor.Contravariant (Op(..))
import safe Data.Foldable (foldl')
import safe Data.Semiring
import safe Data.Semimodule
import safe Data.Semimodule.Algebra
import safe Prelude hiding (Num(..), Fractional(..), init, negate, sum, product)
import safe Control.Monad (MonadPlus(..))

infixr 3 !*

-- | Apply a covector to a vector.
--
(!*) :: Cov a b -> Vec a b -> a
(!*) f = runCov f . runVec

infixl 3 *!

-- | Apply a covector to a vector.
--
(*!) :: Vec a b -> Cov a b -> a 
(*!) = flip (!*)

-- | Obtain a linear transfromation from a vector of covectors.
--
toTran :: Vec (Cov a c) b -> Tran a b c
toTran f = Tran $ \k b -> runCov (runVec f b) k

-- | Obtain a vector of covectors from a linear transformation.
--
fromTran :: Tran a b c -> Vec (Cov a c) b
fromTran m = Op $ \b -> Cov $ \k -> (m !# k) b

-------------------------------------------------------------------------------
-- Vectors
-------------------------------------------------------------------------------

-- | A vector in a vector space or free semimodule.
--
-- Vectors transform contravariantly as a function of their bases.
--
-- See < https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors#Definition >.
--
type Vec = Op

infixr 3 `runVec`

-- | Retrieve the underlying basis function from a vector.
--
runVec :: Vec a b -> b -> a
runVec = getOp

-- | Obtain a vector from an array of coefficients and a basis.
--
vec :: Free f => f a -> Vec a (Base f)
vec = Op . index

-- | Use a linear transformation to map over a vector space.
--
-- Note that the basis transforms < https://en.wikipedia.org/wiki/Covariant_transformation#Contravariant_transformation > contravariantly.
--
vmap :: Tran a b c -> Vec a c -> Vec a b
vmap f g = Op $ runTran f (runVec g)

-- | Obtain a vector from a vector on the tensor product space.
--
join :: Algebra a b => Vec a (b, b) -> Vec a b
join = vmap diagonal

-- | Obtain a vector from the unit of a unital algebra.
--
-- @
-- 'init' a = 'vmap' 'initial' ('Op' $ \_ -> a)
-- @
--
init :: Unital a b => a -> Vec a b
init = Op . unital

-------------------------------------------------------------------------------
-- Covectors
-------------------------------------------------------------------------------

infixr 3 `runCov`

-- | Linear functionals from elements of a free semimodule to a scalar.
--
-- @ 
-- f '!*' (x '+' y) = (f '!*' x) '+' (f '!*' y)
-- f '!*' (x '.*' a) = a '*' (f '!*' x)
-- @
--
-- /Caution/: You must ensure these laws hold when using the default constructor.
--
-- Co-vectors transform covariantly as a function of their bases.
--
-- See < https://en.wikipedia.org/wiki/Covariance_and_contravariance_of_vectors#Definition >.
--
newtype Cov a c = Cov { runCov :: (c -> a) -> a }

-- | Obtain a covector from an array of coefficients and a basis.
--
-- >>> cov (V2 3 4) !* vec (V2 1 2) :: Int
-- 11
--
cov :: FreeCounital a f => f a -> Cov a (Base f)
cov f = Cov $ \k -> f `inner` tabulate k

-- | Use a linear transformation to map over a dual space.
--
-- Note that the basis transforms < https://en.wikipedia.org/wiki/Covariant_transformation covariantly >.
--
cmap :: Tran a b c -> Cov a b -> Cov a c
cmap f g = Cov $ runCov g . runTran f

-- | Obtain a covector from a covector on the tensor product space.
--
cojoin :: Coalgebra a c => Cov a (c, c) -> Cov a c
cojoin = cmap codiagonal

-- | Obtain a covector from the counit of a counital coalgebra.
--
-- @
-- 'coinit' = 'cmap' 'coinitial' ('Cov' $ \f -> f ())
-- @
--
coinit :: Counital a c => Cov a c
coinit = Cov counital

-- | Obtain a covector from a linear combination of basis elements.
--
-- >>> images [(2, E31),(3, E32)] !* vec (V3 1 1 1) :: Int
-- 5
--
images :: Semiring a => Foldable f => f (a, c) -> Cov a c
images f = Cov $ \k -> foldl' (\acc (a, c) -> acc + a * k c) zero f 

-------------------------------------------------------------------------------
-- Cov instances
-------------------------------------------------------------------------------

instance Functor (Cov a) where
  fmap f m = Cov $ \k -> m `runCov` k . f

instance Applicative (Cov a) where
  pure a = Cov $ \k -> k a
  mf <*> ma = Cov $ \k -> mf `runCov` \f -> ma `runCov` k . f

instance Monad (Cov a) where
  return a = Cov $ \k -> k a
  m >>= f = Cov $ \k -> m `runCov` \a -> f a `runCov` k

instance (Additive-Monoid) a => Alternative (Cov a) where
  Cov m <|> Cov n = Cov $ m + n
  empty = Cov zero

instance (Additive-Monoid) a => MonadPlus (Cov a) where
  Cov m `mplus` Cov n = Cov $ m + n
  mzero = Cov zero

instance (Additive-Semigroup) a => Semigroup (Additive (Cov a b)) where
  (<>) = liftA2 $ \(Cov m) (Cov n) -> Cov $ m + n

instance (Additive-Monoid) a => Monoid (Additive (Cov a b)) where
  mempty = Additive $ Cov zero

instance Coalgebra a b => Semigroup (Multiplicative (Cov a b)) where
  (<>) = liftA2 $ \(Cov f) (Cov g) -> Cov $ \k -> f (\m -> g (cojoined k m))

instance Counital a b => Monoid (Multiplicative (Cov a b)) where
  mempty = Multiplicative $ Cov counital

instance Coalgebra a b => Presemiring (Cov a b)

instance Counital a b => Semiring (Cov a b)

instance (Additive-Group) a => Magma (Additive (Cov a b)) where
  (<<) = liftA2 $ \(Cov m) (Cov n) -> Cov $ m - n

instance (Additive-Group) a => Quasigroup (Additive (Cov a b)) where
instance (Additive-Group) a => Loop (Additive (Cov a b)) where
instance (Additive-Group) a => Group (Additive (Cov a b)) where

instance (Ring a, Counital a b) => Ring (Cov a b)

instance Counital r m => LeftSemimodule (Cov r m) (Cov r m) where
  lscale = (*)

instance LeftSemimodule r s => LeftSemimodule r (Cov s m) where
  lscale s m = Cov $ \k -> s *. runCov m k

instance Counital r m => RightSemimodule (Cov r m) (Cov r m) where
  rscale = (*)

instance RightSemimodule r s => RightSemimodule r (Cov s m) where
  rscale s m = Cov $ \k -> runCov m k .* s
