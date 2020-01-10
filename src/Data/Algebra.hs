{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE Safe                  #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE CPP #-}

{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFunctor              #-}

module Data.Algebra where

import safe Data.Bool
import safe Data.Complex
import safe Data.Fixed
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Int
import safe Data.Prd (Prd)
import safe Data.Semigroup (stimes)
import safe Data.Semigroup.Foldable as Foldable1
import safe Data.Tuple
import safe Data.Word
import safe GHC.Real hiding (Fractional(..), (^^), (^))
import safe Numeric.Natural
import safe Foreign.C.Types (CFloat(..),CDouble(..))

import Prelude ( Eq(..), Ord(..), Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), (.), ($), flip, (<$>), Integer, fromInteger, Float, Double)
import qualified Prelude as P

import GHC.Generics (Generic)
{- TODO

- update classes

- figure out how to write numeric literals. maybe quasiquoters? 

- Semimodule w/ (.*), (*.) & dot product (.*.)

- Matrix mult (.#), (#.), (.#.)

- use (#) or (><) for non-associative multiplications, Magma class?

- raid algebra for more newtype ideas

- raid https://github.com/ekmett/abelian/tree/master/src
https://www.youtube.com/watch?v=Nv5tf8pvgrY


- move Lattice to rings?

- update connections lattice, Minimal, Maximal:

type M a = ((Meet-CommutativeBand) a)
type Minimal a = ((Meet-Monoid) a)
type Maximal a = ((Join-Monoid) a)

type Lattice a = (Join–Semilattice a, Meet–Semilattice a)

type CommutativeBand a = (Commutative a, Band a)



class Magma a => AbelianMagma a
class Magma a => DivisibleMagma a
class Magma a => PowerAssociative a
class Magma a => IdempotentMagma a
--type Semigroup a = Associative a
class PowerAssociative a => Associative a


https://en.wikipedia.org/wiki/Magma_(algebra)
https://en.wikipedia.org/wiki/Alternativity
https://en.wikipedia.org/wiki/Power_associativity
https://en.wikipedia.org/wiki/Medial_magma
https://en.wikipedia.org/wiki/Unipotent





-- A quasigroup is semisymmetric if the following equivalent identities hold:
{-
    x << y = y // x,
    y << x = x \\ y,
    x = (y << x) << y,
    x = y << (x << y).
-}
class Quasigroup a => Semisymmetric a

{-
A narrower class that is a totally symmetric quasigroup (sometimes abbreviated TS-quasigroup) in which all conjugates coincide as one operation: xy = x / y = x \ y. Another way to define (the same notion of) totally symmetric quasigroup is as a semisymmetric quasigroup which also is commutative, i.e. xy = yx.

-- x << y = x // y = x \\ y.
-}
type Symmetric a = (Semisymmetric a, AbelianMagma a)

{-
Idempotent total symmetric quasigroups are precisely (i.e. in a bijection with) Steiner triples, so such a quasigroup is also called a Steiner quasigroup, and sometimes the latter is even abbreviated as squag; the term sloop is defined similarly for a Steiner quasigroup that is also a loop. Without idempotency, total symmetric quasigroups correspond to the geometric notion of extended Steiner triple, also called Generalized Elliptic Cubic Curve (GECC). 

< https://en.wikipedia.org/wiki/Steiner_system >
-}
type Steiner a = (Symmetric a, IdempotentMagma a)
type Sloop a = (Steiner a, Loop a)

{-
A quasigroup (Q, <<) is called totally anti-symmetric if for all c, x, y ∈ Q, both of the following implications hold:

    (c << x) << y == (c << y) << x ==> x == y
    x << y == y << x ==> x == y

It is called weakly totally anti-symmetric if only the first implication holds.[5]

This property is required, for example, in the < https://en.wikipedia.org/wiki/Damm_algorithm Damm algorithm >. 
-}
class Quasigroup a => Antisymmetric a




-- https://en.wikipedia.org/wiki/Bol_loop
-- x << (y << (x << z)) = (x << (y << x)) << z     for each x, y and z in Q (a left Bol loop)
class Loop a => LeftBol a

-- ((z << x) << y) << x = z << ((x << y) << x)     for each x, y and z in Q (a right Bol loop)
class Loop a => RightBol a

{-

A loop that is both a left and right Bol loop is a Moufang loop. 
This is equivalent to any one of the following single Moufang identities holding for all x, y, z:

x << (y << (x << z)) = ((x << y) << x) << z,
z << (x << (y << x)) = ((z << x) << y) << x,
(x << y) << (z << x) = x << ((y << z) << x), or
(x << y) << (z << x) = (x << (y << z)) << x.

-}
-- The nonzero octonions form a nonassociative Moufang loop under multiplication.
class (LeftBol a, RightBol a) => Moufang a





-- Unit element of a loop or unital algebra.
--
unit :: (Multiplicative–Loop) a => a 
unit = getProduct lempty

< https://en.wikipedia.org/wiki/Planar_ternary_ring >

-- The structure ( R , ++ ) is a loop with identity element /zero'/. 
-- The set R 0 = R ∖ { 0 } is closed under this multiplication. The structure ( R 0 , ** ) {\displaystyle (R_{0},\otimes )} (R_{{0}},\otimes ) is also a loop, with identity element 1. 
class Ternary a where
  t :: a -> a -> a -> a
  zero' :: a
  one' :: a


a ++ b = t a one' b
a ** b = t a b zero'

-- ? type Planar a = ((Additive–Ternary) a, (Multiplicative–Ternary) a)

-- | < https://en.wikipedia.org/wiki/Planar_ternary_ring#Linear_PTR >
--
-- @ 't' a b c = (a '#' b) '%' c @
--
-- ? type Linear a = ((Additive–Loop) a, (Multiplicative–Loop) a)

instance Ternary a => (Additive–Loop) a where
  t = 


-- in Data.Group

-- | An commutative semigroup.
--
class Semigroup a => Commutative a

-- | An idempotent semigroup.
--
-- < https://en.wikipedia.org/wiki/Band_(mathematics) >
--
class Semigroup a => Idempotent a

-- | An cancellative semigroup.
--
-- https://en.wikipedia.org/wiki/Cancellation_property
class Semigroup a => Cancellative a

type CommutativeMonoid a = (Commutative a, Monoid a)

type CommutativeGroup a = (Commutative a, Group a)

type Semilattice a = (Commutative a, Idempotent a)
-}

-- TODO: Can give Float/Double instances directly.
class Magma a where
  (<<) :: a -> a -> a
  --default (<<) :: Group a => a -> a -> a
  --x << y = x <> inv y

-- (<<) has the < https://en.wikipedia.org/wiki/Latin_square_property >.
-- The unique solutions to these equations are written x = a \\ b and y = b // a. The operations '\\' and '//' are called, respectively, left and right division. 

-- https://en.wikipedia.org/wiki/Quasigroup
-- in a group (//) = (\\) = (<>)
class Magma a => Quasigroup a where
  (//) :: a -> a -> a
  default (//) :: Semigroup a => a -> a -> a
  (//) = (<>)

  (\\) :: a -> a -> a
  default (\\) :: Semigroup a => a -> a -> a
  (\\) = (<>)

{-
Every group is a loop, because a ∗ x = b if and only if x = a−1 ∗ b, and y ∗ a = b if and only if y = b ∗ a−1.
The integers Z with subtraction (−) form a quasigroup.
The nonzero rationals Q× (or the nonzero reals R×) with division (÷) form a quasigroup.
https://en.wikipedia.org/wiki/Mathematics_of_Sudoku#Sudokus_from_group_tables
-}
class Quasigroup a => Loop a where

  lempty :: a
  default lempty :: Monoid a => a
  lempty = mempty

  lreplicate :: Natural -> a -> a
  default lreplicate :: Group a => Natural -> a -> a
  lreplicate n = mreplicate n . inv



--  x << y = x <> inv y
--  inv x = mempty << x
class (Loop a, Monoid a) => Group a where

  inv :: a -> a
  inv x = mempty << x

  greplicate :: Integer -> a -> a
  greplicate n a     
      | n == 0 = mempty
      | n > 0 = mreplicate (P.fromInteger n) a
      | otherwise = mreplicate (P.fromInteger $ P.abs n) (inv a)

newtype Additive a = Sum { getSum :: a }
  deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Additive where
  pure = Sum
  Sum f <*> Sum a = Sum (f a)

infixr 1 –

-- | Greg Pfeil's hyphenation operator.
type (g – f) a = f (g a)  

zero :: (Additive–Monoid) a => a
zero = getSum mempty

infixl 6 +, -

(+) :: (Additive–Semigroup) a => a -> a -> a
a + b = getSum (Sum a <> Sum b)
{-# INLINE (+) #-}

(-) :: (Additive–Group) a => a -> a -> a
a - b = getSum (Sum a << Sum b)
{-# INLINE (-) #-}

negate :: (Additive–Group) a => a -> a
negate a = zero - a
{-# INLINE negate #-}

-- | A generalization of 'Data.List.replicate' to an arbitrary 'Monoid'. 
--
-- Adapted from <http://augustss.blogspot.com/2008/07/lost-and-found-if-i-write-108-in.html>.
--
mreplicate :: Monoid a => Natural -> a -> a
mreplicate n a
    | n == 0 = mempty
    | otherwise = f a n
    where
        f x y 
            | even y = f (x <> x) (y `quot` 2)
            | y == 1 = x
            | otherwise = g (x <> x) ((y P.- 1) `quot` 2) x
        g x y z 
            | even y = g (x <> x) (y `quot` 2) z
            | y == 1 = x <> z
            | otherwise = g (x <> x) ((y P.- 1) `quot` 2) (x <> z)
{-# INLINE mreplicate #-}


-- https://en.wikipedia.org/wiki/Linearly_ordered_group
abs :: (Additive–Group) a => Ord a => a -> a
abs x = bool (negate x) x $ zero <= x
{-# INLINE abs #-}

-- in Data.Ring
type Presemiring a = ((Additive–Semigroup) a, (Multiplicative–Semigroup) a)

type Rig a = ((Additive–Monoid) a, (Multiplicative–Monoid) a)

type Unital a = Rig a --((Additive–Monoid) a, (Multiplicative–Monoid) a)

--https://en.wikipedia.org/wiki/Rng_(algebra)
type Rng a = ((Additive–Group) a, (Multiplicative–Semigroup) a)

type Semiring a = ((Additive–Monoid) a, (Multiplicative–Semigroup) a)

type Ring a = ((Additive–Group) a, (Multiplicative–Monoid) a)

class (Prd a, Semiring a) => Dioid a

--class Semiring a => Involutive a where adjoint :: a -> a

--type InvolutiveSemiring a = (Involutive a, Semiring a)

--type AdditiveIdempotentSemiring a = ((Additive–Idempotent) a, Semiring a)


infixl 7 *

(*) :: (Multiplicative–Semigroup) a => a -> a -> a
a * b = getProduct (Product a <> Product b)
{-# INLINE (*) #-}

infixr 8 ^

-- @ 'one' == a '^' 0 @
--
-- >>> 8 ^ 0 :: Int
-- 1
--
(^) :: (Multiplicative–Monoid) a => a -> Natural -> a
a ^ n = getProduct $ mreplicate (P.fromIntegral n) (Product a)

infixr 8 ^^

-- @ 'one' == a '^^' 0 @
--
-- >>> 8 ^^ 0 :: Double
-- 1.0
-- >>> 8 ^^ 0 :: Pico
-- 1.000000000000
--
(^^) :: (Multiplicative–Group) a => a -> Integer -> a
a ^^ n = getProduct $ greplicate n (Product a)


one :: (Multiplicative–Monoid) a => a
one = getProduct mempty

signum :: Ring a => Ord a => a -> a
signum x = bool (negate one) one $ zero <= x
{-# INLINE signum #-}

newtype Multiplicative a = Product { getProduct :: a }
  deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Multiplicative where
  pure = Product
  Product f <*> Product a = Product (f a)


-- in Data.Field
-- Sometimes called a division ring
type Semifield a = ((Additive–Monoid) a, (Multiplicative–Group) a)

type Field a = ((Additive–Group) a, (Multiplicative–Group) a)

infixl 7 /

(/) :: (Multiplicative–Group) a => a -> a -> a
a / b = getProduct (Product a << Product b)
{-# INLINE (/) #-}


-- | Take the reciprocal of a multiplicative group element.
--
-- >>> recip (3 :+ 4) :: Complex Rational
-- 3 % 25 :+ (-4) % 25
-- >>> recip (3 :+ 4) :: Complex Double
-- 0.12 :+ (-0.16)
-- >>> recip (3 :+ 4) :: Complex Pico
-- 0.120000000000 :+ -0.160000000000
-- 
recip :: (Multiplicative–Group) a => a -> a 
recip a = one / a
{-# INLINE recip #-}

type Positive = Ratio Natural


type Module r a = (Ring r, Group a, Semimodule r a)

infixl 7 .*, *.

class (Semiring r, Semigroup a) => Semimodule r a where

  -- | Left-multiply by a scalar.
  --
  (.*) :: a -> r -> a
  (.*) = flip (*.)
  
  -- | Right-multiply by a scalar.
  --
  (*.) :: r -> a -> a
  (*.) = flip (.*)


-- | Linearly interpolate between two vectors.
--
lerp :: Module r a => r -> a -> a -> a
lerp r f g = r *. f <> (one - r) *. g
{-# INLINE lerp #-}



-- in Data.Algebra

infixl 6 %
(%) :: (Additive–Magma) a => a -> a -> a
a % b = getSum (Sum a << Sum b)
{-# INLINE (%) #-}

infixl 7 #
-- Use for non-associative algebra operations like cross-product.
(#) :: (Multiplicative–Magma) a => a -> a -> a
a # b = getProduct (Product a << Product b)
{-# INLINE (#) #-}




---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------


instance Presemiring a => Semigroup (Additive (Ratio a)) where
  Sum (a :% b) <> Sum (c :% d) = Sum $ (a*d + c*b) :% (b * d)
  {-# INLINE (<>) #-}

instance Unital a => Monoid (Additive (Ratio a)) where
  mempty = Sum $ zero :% one

instance Ring a => Magma (Additive (Ratio a)) where
  Sum (a :% b) << Sum (c :% d) = Sum $ (a*d - c*b) :% (b * d)
  {-# INLINE (<<) #-}

instance Ring a => Quasigroup (Additive (Ratio a))

instance Ring a => Loop (Additive (Ratio a))

instance Ring a => Group (Additive (Ratio a))

instance (Multiplicative–Semigroup) a => Semigroup (Multiplicative (Ratio a)) where
  Product (a :% b) <> Product (c :% d) = Product $ (a * c) :% (b * d)
  {-# INLINE (<>) #-}

instance (Multiplicative–Monoid) a => Monoid (Multiplicative (Ratio a)) where
  mempty = Product $ one :% one

instance (Multiplicative–Monoid) a => Magma (Multiplicative (Ratio a)) where
  Product (a :% b) << Product (c :% d) = Product $ (a * d) :% (b * c)
  {-# INLINE (<<) #-}

instance (Multiplicative–Monoid) a => Quasigroup (Multiplicative (Ratio a))

instance (Multiplicative–Monoid) a => Loop (Multiplicative (Ratio a))

instance (Multiplicative–Monoid) a => Group (Multiplicative (Ratio a))

instance (Additive–Semigroup) a => Semigroup (Additive (Complex a)) where
  Sum (a :+ b) <> Sum (c :+ d) = Sum $ (a + b) :+ (c + d)
  {-# INLINE (<>) #-}

instance (Additive–Monoid) a => Monoid (Additive (Complex a)) where
  mempty = Sum $ zero :+ zero

instance (Additive–Group) a => Magma (Additive (Complex a)) where
  Sum (a :+ b) << Sum (c :+ d) = Sum $ (a - c) :+ (b - d)
  {-# INLINE (<<) #-}

instance (Additive–Group) a => Quasigroup (Additive (Complex a))

instance (Additive–Group) a => Loop (Additive (Complex a))

instance (Additive–Group) a => Group (Additive (Complex a))

instance Rng a => Semigroup (Multiplicative (Complex a)) where
  Product (a :+ b) <> Product (c :+ d) = Product $ (a*c - b*d) :+ (a*d + b*c)
  {-# INLINE (<>) #-}

instance Ring a => Monoid (Multiplicative (Complex a)) where
  mempty = Product $ one :+ zero

instance Field a => Magma (Multiplicative (Complex a)) where
  Product (a :+ b) << Product (c :+ d) = Product $ (a*c + b*d) / (c*c + d*d) :+ (b*c - a*d) / (c*c + d*d)
  {-# INLINE (<<) #-}

instance Field a => Quasigroup (Multiplicative (Complex a))

instance Field a => Loop (Multiplicative (Complex a))

instance Field a => Group (Multiplicative (Complex a))


#define deriveAdditiveSemigroup(ty)             \
instance Semigroup (Additive ty) where {        \
   a <> b = (P.+) <$> a <*> b                   \
;  {-# INLINE (<>) #-}                          \
}

deriveAdditiveSemigroup(Int)
deriveAdditiveSemigroup(Int8)
deriveAdditiveSemigroup(Int16)
deriveAdditiveSemigroup(Int32)
deriveAdditiveSemigroup(Int64)
deriveAdditiveSemigroup(Integer)

deriveAdditiveSemigroup(Word)
deriveAdditiveSemigroup(Word8)
deriveAdditiveSemigroup(Word16)
deriveAdditiveSemigroup(Word32)
deriveAdditiveSemigroup(Word64)
deriveAdditiveSemigroup(Natural)

deriveAdditiveSemigroup(Uni)
deriveAdditiveSemigroup(Deci)
deriveAdditiveSemigroup(Centi)
deriveAdditiveSemigroup(Milli)
deriveAdditiveSemigroup(Micro)
deriveAdditiveSemigroup(Nano)
deriveAdditiveSemigroup(Pico)

deriveAdditiveSemigroup(Float)
deriveAdditiveSemigroup(CFloat)
deriveAdditiveSemigroup(Double)
deriveAdditiveSemigroup(CDouble)

#define deriveMultiplicativeSemigroup(ty)       \
instance Semigroup (Multiplicative ty) where {  \
   a <> b = (P.*) <$> a <*> b                   \
;  {-# INLINE (<>) #-}                          \
}

deriveMultiplicativeSemigroup(Int)
deriveMultiplicativeSemigroup(Int8)
deriveMultiplicativeSemigroup(Int16)
deriveMultiplicativeSemigroup(Int32)
deriveMultiplicativeSemigroup(Int64)
deriveMultiplicativeSemigroup(Integer)

deriveMultiplicativeSemigroup(Word)
deriveMultiplicativeSemigroup(Word8)
deriveMultiplicativeSemigroup(Word16)
deriveMultiplicativeSemigroup(Word32)
deriveMultiplicativeSemigroup(Word64)
deriveMultiplicativeSemigroup(Natural)

deriveMultiplicativeSemigroup(Uni)
deriveMultiplicativeSemigroup(Deci)
deriveMultiplicativeSemigroup(Centi)
deriveMultiplicativeSemigroup(Milli)
deriveMultiplicativeSemigroup(Micro)
deriveMultiplicativeSemigroup(Nano)
deriveMultiplicativeSemigroup(Pico)

deriveMultiplicativeSemigroup(Float)
deriveMultiplicativeSemigroup(CFloat)
deriveMultiplicativeSemigroup(Double)
deriveMultiplicativeSemigroup(CDouble)

#define deriveAdditiveMonoid(ty)                \
instance Monoid (Additive ty) where {           \
   mempty = pure 0                              \
;  {-# INLINE mempty #-}                        \
}

deriveAdditiveMonoid(Int)
deriveAdditiveMonoid(Int8)
deriveAdditiveMonoid(Int16)
deriveAdditiveMonoid(Int32)
deriveAdditiveMonoid(Int64)
deriveAdditiveMonoid(Integer)

deriveAdditiveMonoid(Word)
deriveAdditiveMonoid(Word8)
deriveAdditiveMonoid(Word16)
deriveAdditiveMonoid(Word32)
deriveAdditiveMonoid(Word64)
deriveAdditiveMonoid(Natural)

deriveAdditiveMonoid(Uni)
deriveAdditiveMonoid(Deci)
deriveAdditiveMonoid(Centi)
deriveAdditiveMonoid(Milli)
deriveAdditiveMonoid(Micro)
deriveAdditiveMonoid(Nano)
deriveAdditiveMonoid(Pico)

deriveAdditiveMonoid(Float)
deriveAdditiveMonoid(CFloat)
deriveAdditiveMonoid(Double)
deriveAdditiveMonoid(CDouble)

#define deriveMultiplicativeMonoid(ty)          \
instance Monoid (Multiplicative ty) where {     \
   mempty = pure 1                              \
;  {-# INLINE mempty #-}                        \
}

deriveMultiplicativeMonoid(Int)
deriveMultiplicativeMonoid(Int8)
deriveMultiplicativeMonoid(Int16)
deriveMultiplicativeMonoid(Int32)
deriveMultiplicativeMonoid(Int64)
deriveMultiplicativeMonoid(Integer)

deriveMultiplicativeMonoid(Word)
deriveMultiplicativeMonoid(Word8)
deriveMultiplicativeMonoid(Word16)
deriveMultiplicativeMonoid(Word32)
deriveMultiplicativeMonoid(Word64)
deriveMultiplicativeMonoid(Natural)

deriveMultiplicativeMonoid(Uni)
deriveMultiplicativeMonoid(Deci)
deriveMultiplicativeMonoid(Centi)
deriveMultiplicativeMonoid(Milli)
deriveMultiplicativeMonoid(Micro)
deriveMultiplicativeMonoid(Nano)
deriveMultiplicativeMonoid(Pico)

deriveMultiplicativeMonoid(Float)
deriveMultiplicativeMonoid(CFloat)
deriveMultiplicativeMonoid(Double)
deriveMultiplicativeMonoid(CDouble)

#define deriveAdditiveMagma(ty)                 \
instance Magma (Additive ty) where {            \
   a << b = (P.-) <$> a <*> b                   \
;  {-# INLINE (<<) #-}                          \
}

deriveAdditiveMagma(Int)
deriveAdditiveMagma(Int8)
deriveAdditiveMagma(Int16)
deriveAdditiveMagma(Int32)
deriveAdditiveMagma(Int64)
deriveAdditiveMagma(Integer)

deriveAdditiveMagma(Uni)
deriveAdditiveMagma(Deci)
deriveAdditiveMagma(Centi)
deriveAdditiveMagma(Milli)
deriveAdditiveMagma(Micro)
deriveAdditiveMagma(Nano)
deriveAdditiveMagma(Pico)

deriveAdditiveMagma(Float)
deriveAdditiveMagma(CFloat)
deriveAdditiveMagma(Double)
deriveAdditiveMagma(CDouble)

#define deriveAdditiveQuasigroup(ty)            \
instance Quasigroup (Additive ty) where {             \
}

deriveAdditiveQuasigroup(Int)
deriveAdditiveQuasigroup(Int8)
deriveAdditiveQuasigroup(Int16)
deriveAdditiveQuasigroup(Int32)
deriveAdditiveQuasigroup(Int64)
deriveAdditiveQuasigroup(Integer)

deriveAdditiveQuasigroup(Uni)
deriveAdditiveQuasigroup(Deci)
deriveAdditiveQuasigroup(Centi)
deriveAdditiveQuasigroup(Milli)
deriveAdditiveQuasigroup(Micro)
deriveAdditiveQuasigroup(Nano)
deriveAdditiveQuasigroup(Pico)

deriveAdditiveQuasigroup(Float)
deriveAdditiveQuasigroup(CFloat)
deriveAdditiveQuasigroup(Double)
deriveAdditiveQuasigroup(CDouble)

#define deriveAdditiveLoop(ty)                  \
instance Loop (Additive ty) where {             \
   lreplicate n (Sum a) = Sum $ P.fromIntegral n * (-a) \
;  {-# INLINE lreplicate #-}                    \
}

deriveAdditiveLoop(Int)
deriveAdditiveLoop(Int8)
deriveAdditiveLoop(Int16)
deriveAdditiveLoop(Int32)
deriveAdditiveLoop(Int64)
deriveAdditiveLoop(Integer)

deriveAdditiveLoop(Uni)
deriveAdditiveLoop(Deci)
deriveAdditiveLoop(Centi)
deriveAdditiveLoop(Milli)
deriveAdditiveLoop(Micro)
deriveAdditiveLoop(Nano)
deriveAdditiveLoop(Pico)

deriveAdditiveLoop(Float)
deriveAdditiveLoop(CFloat)
deriveAdditiveLoop(Double)
deriveAdditiveLoop(CDouble)

#define deriveAdditiveGroup(ty)                 \
instance Group (Additive ty) where {            \
   greplicate n (Sum a) = Sum $ P.fromInteger n * a \
;  {-# INLINE greplicate #-}                    \
}

deriveAdditiveGroup(Int)
deriveAdditiveGroup(Int8)
deriveAdditiveGroup(Int16)
deriveAdditiveGroup(Int32)
deriveAdditiveGroup(Int64)
deriveAdditiveGroup(Integer)

deriveAdditiveGroup(Uni)
deriveAdditiveGroup(Deci)
deriveAdditiveGroup(Centi)
deriveAdditiveGroup(Milli)
deriveAdditiveGroup(Micro)
deriveAdditiveGroup(Nano)
deriveAdditiveGroup(Pico)

deriveAdditiveGroup(Float)
deriveAdditiveGroup(CFloat)
deriveAdditiveGroup(Double)
deriveAdditiveGroup(CDouble)

#define deriveMultiplicativeMagma(ty)                 \
instance Magma (Multiplicative ty) where {            \
   a << b = (P./) <$> a <*> b                   \
;  {-# INLINE (<<) #-}                          \
}

deriveMultiplicativeMagma(Uni)
deriveMultiplicativeMagma(Deci)
deriveMultiplicativeMagma(Centi)
deriveMultiplicativeMagma(Milli)
deriveMultiplicativeMagma(Micro)
deriveMultiplicativeMagma(Nano)
deriveMultiplicativeMagma(Pico)

deriveMultiplicativeMagma(Float)
deriveMultiplicativeMagma(CFloat)
deriveMultiplicativeMagma(Double)
deriveMultiplicativeMagma(CDouble)

#define deriveMultiplicativeQuasigroup(ty)            \
instance Quasigroup (Multiplicative ty) where {             \
}

deriveMultiplicativeQuasigroup(Uni)
deriveMultiplicativeQuasigroup(Deci)
deriveMultiplicativeQuasigroup(Centi)
deriveMultiplicativeQuasigroup(Milli)
deriveMultiplicativeQuasigroup(Micro)
deriveMultiplicativeQuasigroup(Nano)
deriveMultiplicativeQuasigroup(Pico)

deriveMultiplicativeQuasigroup(Float)
deriveMultiplicativeQuasigroup(CFloat)
deriveMultiplicativeQuasigroup(Double)
deriveMultiplicativeQuasigroup(CDouble)

#define deriveMultiplicativeLoop(ty)                  \
instance Loop (Multiplicative ty) where {             \
}

deriveMultiplicativeLoop(Uni)
deriveMultiplicativeLoop(Deci)
deriveMultiplicativeLoop(Centi)
deriveMultiplicativeLoop(Milli)
deriveMultiplicativeLoop(Micro)
deriveMultiplicativeLoop(Nano)
deriveMultiplicativeLoop(Pico)

deriveMultiplicativeLoop(Float)
deriveMultiplicativeLoop(CFloat)
deriveMultiplicativeLoop(Double)
deriveMultiplicativeLoop(CDouble)

#define deriveMultiplicativeGroup(ty)           \
instance Group (Multiplicative ty) where {      \
   greplicate n (Product a) = Product $ a P.^^ P.fromInteger n \
;  {-# INLINE greplicate #-}                    \
}

deriveMultiplicativeGroup(Uni)
deriveMultiplicativeGroup(Deci)
deriveMultiplicativeGroup(Centi)
deriveMultiplicativeGroup(Milli)
deriveMultiplicativeGroup(Micro)
deriveMultiplicativeGroup(Nano)
deriveMultiplicativeGroup(Pico)

deriveMultiplicativeGroup(Float)
deriveMultiplicativeGroup(CFloat)
deriveMultiplicativeGroup(Double)
deriveMultiplicativeGroup(CDouble)
