{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE Safe                  #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE Safe                       #-}

module Data.Magma where

import safe Data.Bool
import safe Data.Complex
import safe Data.Fixed
import safe Data.Foldable as Foldable (fold, foldl')
import safe Data.Int
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

type Lattice a = (Join-Semilattice a, Meet-Semilattice a)

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
unit :: (Multiplicative-Loop) a => a 
unit = unMultiplicative lempty

< https://en.wikipedia.org/wiki/Planar_ternary_ring >

-- The structure ( R , ++ ) is a loop with identity element /zero'/. 
-- The set R 0 = R ∖ { 0 } is closed under this multiplication. The structure ( R 0 , ** ) {\displaystyle (R_{0},\otimes )} (R_{{0}},\otimes ) is also a loop, with identity element 1. 
class Ternary a where
  t :: a -> a -> a -> a
  zero' :: a
  one' :: a


a ++ b = t a one' b
a ** b = t a b zero'

-- ? type Planar a = ((Additive-Ternary) a, (Multiplicative-Ternary) a)

-- | < https://en.wikipedia.org/wiki/Planar_ternary_ring#Linear_PTR >
--
-- @ 't' a b c = (a '#' b) '%' c @
--
-- ? type Linear a = ((Additive-Loop) a, (Multiplicative-Loop) a)

instance Ternary a => (Additive-Loop) a where
  t = 


-- in Data.Group

-- | A commutative semigroup.
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

infixl 6 <<

-- TODO: Can give Float/Double instances directly.
-- When /a/ is a 'Group' we must have:
-- @ x '<<' y = x '<>' 'inv' y @
class Magma a where
  (<<) :: a -> a -> a




--instance Magma a => Magma (Maybe a)
