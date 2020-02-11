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
-}
import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Distributive
import safe Data.Fixed
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Functor.Compose
import safe Data.Functor.Rep
 hiding ((//))
import safe Data.Int
import safe Data.Semifield
import safe Data.Semigroup.Additive as A
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Semigroup.Multiplicative as M
import safe Data.Semimodule
import safe Data.Semiring
import safe Data.Tuple
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Real hiding (Fractional(..))
import safe Numeric.Natural
import safe Prelude hiding (Num(..), Fractional(..), sum, product)
import safe Test.Logic
import safe qualified Prelude as P

-- | < https://en.wikipedia.org/wiki/Algebra_over_a_field#Generalization:_algebra_over_a_ring Algebra > over a semiring.
--
-- Needn't be associative or unital.
--
class Semiring r => Algebra r a where
  multiplyWith :: (a -> a -> r) -> a -> r

infixl 7 ><

-- | Multiplication operator on a free algebra.
--
-- In particular this is cross product on the 'I3' basis in /R^3/:
--
-- >>> V3 1 0 0 >< V3 0 1 0 >< V3 0 1 0 :: V3 Int
-- V3 (-1) 0 0
-- >>> V3 1 0 0 >< (V3 0 1 0 >< V3 0 1 0) :: V3 Int
-- V3 0 0 0
--
-- /Caution/ in general (><) needn't be commutative, nor even associative.
--
-- The cross product in particular satisfies the following properties:
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
--
(><) :: (Representable f, Algebra r (Rep f)) => f r -> f r -> f r
(><) x y = tabulate $ multiplyWith (\i1 i2 -> index x i1 * index y i2)

-- | Scalar triple product.
--
-- @
-- 'triple' x y z = 'triple' z x y = 'triple' y z x
-- 'triple' x y z = 'negate' '$' 'triple' x z y = 'negate' '$' 'triple' y x z
-- 'triple' x x y = 'triple' x y y = 'triple' x y x = 'zero'
-- ('triple' x y z) '*.' x = (x '><' y) '><' (x '><' z)
-- @
--
-- >>> triple (V3 0 0 1) (V3 1 0 0) (V3 0 1 0) :: Double
-- 1.0
--
triple :: Free f => Foldable f => Algebra a (Rep f) => f a -> f a -> f a -> a
triple x y z = x .*. (y >< z)
{-# INLINE triple #-}

-- | < https://en.wikipedia.org/wiki/Composition_algebra Composition algebra > over a free semimodule.
--
class Algebra r a => Composition r a where
  conjugateWith :: (a -> r) -> a -> r

  normWith :: (a -> r) -> r
  

-- @ 'conj' a '><' 'conj' b = 'conj' (b >< a) @
prop_conj :: Representable f => Foldable f => Semiring b => Composition a (Rep f) => Rel a b -> f a -> f a -> b
prop_conj (~~) p q = sum $ mzipWithRep (~~) (conj (p >< q)) (conj q >< conj p)

-- @ 'conj' a '><' 'conj' b = 'conj' (b >< a) @
conj :: Representable f => Composition r (Rep f) => f r -> f r
conj = tabulate . conjugateWith . index

-- | Norm of a composition algebra.
--
-- @ 
-- 'norm' x '*' 'norm' y = 'norm' (x >< y)
-- 'norm' . 'norm'' $ x = 'norm' x '*' 'norm' x
-- @
--
norm :: (Representable f, Composition r (Rep f)) => f r -> r
norm x = normWith $ index x

norm' :: (Representable f, Composition r (Rep f)) => f r -> f r
norm' x = x >< conj x

class (Semiring r, Algebra r a) => Unital r a where
  unitWith :: r -> a -> r

-- | Unit of a unital algebra.
--
-- >>> unit :: Complex Int
-- 1 :+ 0
-- >>> unit :: QuatD
-- Quaternion 1.0 (V3 0.0 0.0 0.0)
--
unit :: Representable f => Unital r (Rep f) => f r
unit = tabulate $ unitWith one

-- | A (not necessarily associative) < https://en.wikipedia.org/wiki/Division_algebra division algebra >.
--
class (Semifield r, Unital r a) => Division r a where
  --divideWith :: (a -> a -> r) -> a -> r

  reciprocalWith :: (a -> r) -> a -> r
  



-- | @ 'reciprocal' x = (/ 'quadrance' x) '<$>' 'conj' x@
reciprocal :: Representable f => Division a (Rep f) => f a -> f a
reciprocal = tabulate . reciprocalWith . index

-- reciprocal' x = (/ quadrance x) <$> conj x


infixl 7 //

-- | Division operator on a free division algebra.
--
-- >>> (1 :+ 0) // (0 :+ 1)
-- 0.0 :+ (-1.0)
--
(//) :: Representable f => Division r (Rep f) => f r -> f r -> f r
(//) x y = x >< reciprocal y

infix 6 .@. 
-- | Bilinear form on a free composition algebra.
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
(.@.) :: Representable f => Composition a (Rep f) => Semigroup (f a) => Field a => f a -> f a -> a
x .@. y = prod / two where prod = norm (x <> y) - norm x - norm y

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

  normWith f = flip multiplyWith zero $ \i1 i2 -> f i1 * conjugateWith f i2

--instance Module r ComplexBasis => Unital r ComplexBasis where
instance Ring r => Unital r ComplexBasis where
  unitWith x False = x
  unitWith _ _ = zero

instance Field r => Division r ComplexBasis where
  reciprocalWith f i = conjugateWith f i / normWith f 
