{-# LANGUAGE Safe                       #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE StandaloneDeriving         #-}
module Data.Semiring.Heyting where

import safe Data.Functor.Alt
import safe Data.Functor.Compose
import safe Data.Functor.Const
import safe Data.Functor.Contravariant
import safe Data.Functor.Identity
import safe Data.Functor.Rep
import safe Data.Prd
import safe Data.Prd.Top
import safe Data.Semiring
import safe Prelude
 ( Eq(..), Ord, IO, Show(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..)
 , id, flip, const, (.), ($), not, Bool, Integer, Float, Double, Maybe(..), Ordering(..) )
import safe Data.IntMap (IntMap)
import safe Data.IntSet (IntSet)
import safe Data.Map (Map)
import safe Data.Set (Set)
import safe Data.Sequence (Seq)
import safe qualified Data.Functor.Product as F
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set

import safe Data.Profunctor
import safe Data.Profunctor.Yoneda
import safe Control.Category (Category)

-- Heyting algebras
--

-- |
-- Heyting algebra is a bounded semi-lattice with implication which should
-- satisfy the following law:
--
-- > x ∧ a ≤ b ⇔ x ≤ (a ⇒ b)
--
-- We also require that a Heyting algebra is a distributive lattice, which
-- means any of the two equivalent conditions holds:
--
-- > a ∧ (b ∨ c) = a ∧ b ∨ a ∧ c
-- > a ∨ (b ∧ c) = (a ∨ b) ∧ (a ∨ c)
--
-- This means @a ⇒ b@ is an [exponential object](https://ncatlab.org/nlab/show/exponential%2Bobject),
-- which makes any Heyting algebra a [cartesian closed category](https://ncatlab.org/nlab/show/cartesian%2Bclosed%2Bcategory).
--
-- This means that Curry isomorphism holds (which takes a form of an actual
-- equality):
--
-- prop> a ⇒ (b ⇒ c) = (a ∧ b) ⇒ c
--
-- Some other useful properties of Heyting algebras:
-- 
-- > (a ⇒ b) ∧ a ≤ b
-- > b ≤ a ⇒ a ∧ b
-- > a ≤ b  iff a ⇒ b = ⊤
-- > b ≤ b' then a ⇒ b ≤ a ⇒ b'
-- > a'≤ a  then a' ⇒ b ≤ a ⇒ b
-- > neg (a ∧ b) = neg (a ∨ b)
-- > neg (a ∨ b) = neg a ∧ neg b
--
class Semiring a => Heyting a where
  infixr 4 ==>

  -- |
  -- Default implementation: @a ==> b = neg a + b@, it requires @neg@ to
  -- satisfy Boolean axioms, which will make it into a Boolean algebra.
  --
  -- Fixity is less than fixity of both @'+'@ and @'*'@.
  (==>) :: a -> a -> a
  (==>) a b = neg a + b

  -- | Logical negation
  neg :: a -> a
  neg a = a ==> zero

  {-# MINIMAL (==>) | neg #-}

-- |
-- @'implies'@ is an alias for @'==>'@
implies :: Heyting a => a -> a -> a
implies = (==>)

(<==>) :: Heyting a => a -> a -> a
a <==> b = (a ==> b) * (b ==> a)

-- | A prefix alias for @'<==>'@

iff :: Heyting a => a -> a -> a
iff = (<==>)

instance Heyting () where
  _ ==> _ = ()

instance Heyting Bool where
  neg = not

-- an example that falsifies the law of excluded middle:
-- > EQ + neg EQ = EQ + (EQ ==> LT) = EQ + LT = EQ  
instance Heyting Ordering where
  LT ==> _ = GT
  EQ ==> LT = LT
  EQ ==> _ = GT
  GT ==> x = x

  neg LT = GT
  neg _ = LT

instance Heyting a => Heyting (Maybe a) where
  Just a ==> Just b = Just $ a ==> b
  Nothing ==> _        = Just one
  _       ==> Nothing  = Nothing

instance Heyting b => Heyting (a -> b) where
  f ==> g = \a -> f a ==> g a

instance Heyting a => Heyting (Op a b) where
  Op f ==> Op g = Op $ \x -> f x ==> g x

instance Heyting (Predicate a) where
  Predicate f ==> Predicate g = Predicate $ \x -> f x <= g x

instance Heyting (Equivalence a) where
  Equivalence f ==> Equivalence g = Equivalence $ \x y -> f x y <= g x y

{-
instance Heyting a => Heyting (Endo a) where
  Endo f ==> Endo g = Endo $ f ==> g
instance Heyting a => Heyting (Identity a) where
  Identity a ==> Identity b = Identity a ==> b
instance Heyting a => Heyting (Const a b) where
  Const a ==> Const b = Const a ==> b
-}

instance (Heyting a, Heyting b) => Heyting (a, b) where
  (a0, b0) ==> (a1, b1) = (a0 ==> a1, b0 ==> b1)

instance (Heyting a, Heyting b, Heyting c) => Heyting (a, b, c) where
  (a0, b0, c0) ==> (a1, b1, c1) = (a0 ==> a1, b0 ==> b1, c0 ==> c1)
--instance Heyting a => Heyting (Down a) where
--  (Down a) ==> (Down b) = Down (neg a * b)


