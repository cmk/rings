{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Semilattice (
  -- * Types
    type (-)
  , Semilattice
  -- * Join semilattices
  , Join(..)
  , bottom
  , (\/)
  , join
  , joinWith
  , join1
  , joinWith1
  --, lower
  , joinLe
  , pcompareJoin
  -- * Meet semilattices
  , Meet(..)
  , top
  , (/\)
  , meet
  , meetWith
  , meet1
  , meetWith1
  --, upper
  , meetLe
  , pcompareMeet
  -- * Lattices
  , LatticeLaw
  , Lattice(..)
  --, eq, ne
  , lt, gt
  , pmax, pmin
  , glb, lub
  , BoundedLatticeLaw
  , BoundedLattice(..)
  -- * Heyting algebras
  , HeytingLaw
  , Heyting(..)
  , (==>)
  , (<==)
  , le

  -- * DerivingVia
  , F1(..)
  , F2(..)
) where

import safe Control.Applicative
import safe Data.Bool hiding (not)
import safe Data.Either
import safe Data.Fixed
import safe Data.Foldable
import safe Data.Functor.Apply
import safe Data.Functor.Compose
import safe Data.Int
import safe Data.Maybe
import safe Data.Ord
import safe Data.Group
import safe Data.Semigroup
import safe Data.Semigroup.Foldable
import safe Data.Semigroup.Traversable
import safe Data.Semigroup.Quantale
import safe Data.Word
import safe Numeric.Natural
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set
import safe Data.Set (Set)

import safe Control.Applicative
import safe Data.Maybe
import safe Data.Either
import safe GHC.Generics (Generic)

import safe Numeric.Natural
import safe Data.Word
import safe Data.Int
import safe Data.Fixed

import safe Prelude hiding (not)
import safe qualified Prelude as P
import safe Data.Kind

import safe Data.Connection
import safe Data.Connection.Conn
import safe Data.Connection.Trip
import safe Data.Universe.Class    (Finite(..))

-- | Hyphenation operator.
type ((g :: Type -> Type) - (f :: Type -> Constraint)) a = f (g a)


joined :: Trip a (Either a a)
joined = Trip Left (either id id) Right

forked :: Lattice a => Trip (a, a) a
forked = Trip (uncurry (\/)) (\x -> (x,x)) (uncurry (/\))

--infixr 3 &&&
--(&&&) :: (Join-Semilattice) c => (Meet-Semilattice) c => Conn c a -> Conn c b -> Conn c (a, b)
--f &&& g = tripr forked >>> f `strong` g

-------------------------------------------------------------------------------
-- Semilattice laws
-------------------------------------------------------------------------------

type Semilattice = Semigroup



-- | Yoneda representation for lattice ideals.
--
-- A subset /I/ of a lattice is an ideal if and only if it is a lower set 
-- that is closed under finite joins, i.e., it is nonempty and for all 
-- /x/, /y/ in /I/, the element /x \/ y/ is also in /I/.
--
-- /upper/ and /lower/ commute with /Down/:
--
-- * @lower x y = upper (Down x) (Down y)@
--
-- * @lower (Down x) (Down y) = upper x y@
--
-- /a/ is downward-closed:
--
-- * @'lower' x s && x '>=' y => 'lower' y s@
--
-- * @'lower' x s && 'lower' y s => 'connl' 'ideal' x '\/' 'connl' 'ideal' y '<=' s@
--
-- Finally /filter >>> ideal/ and /ideal >>> filter/ are both connections
-- on /a/ and /Idx a/ respectively.
--
-- See <https://en.wikipedia.org/wiki/Ideal_(order_theory)>
--
type Ideal a b = (Connection a b, Eq a, (Join-Semilattice) a)
--type SetIdeal a b = Ideal (Set a) b
--type SetFilter a b = Filter a (Set b)

-- | Yoneda representation for lattice filters.
--
-- A subset /I/ of a lattice is an filter if and only if it is an upper set 
-- that is closed under finite meets, i.e., it is nonempty and for all 
-- /x/, /y/ in /I/, the element /x /\ y/ is also in /I/.
--
-- /upper/ and /lower/ commute with /Down/:
--
-- * @lower x y = upper (Down x) (Down y)@
--
-- * @lower (Down x) (Down y) = upper x y@
--
-- /b/ is upward-closed:
--
-- * @'upper' x s && x '<=' y => 'upper' y s@
--
-- * @'upper' x s && 'upper' y s => 'connl' 'filter' x '/\' 'connl' 'filter' y '>=' s@
--
-- See <https://en.wikipedia.org/wiki/Filter_(mathematics)>
--
type Filter a b = (Connection a b, Eq b, (Meet-Semilattice) b)


-------------------------------------------------------------------------------
-- Join semilattices
-------------------------------------------------------------------------------


-- | A commutative 'Semilattice' under '\/'.
newtype Join a = Join { getJoin :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Join where
  pure = Join
  Join f <*> Join a = Join (f a)

bottom :: (Join-Monoid) a => a
bottom = getJoin mempty
{-# INLINE bottom #-}

infixr 5 \/

-- | Join operation on a semilattice.
--
-- >>> (> (0::Int)) ∧ ((< 10) \/ (== 15)) $ 10
-- False
--
-- >>> IntSet.fromList [1..5] ∧ IntSet.fromList [2..5]
-- fromList [2,3,4,5]
(\/) :: (Join-Semilattice) a => a -> a -> a
a \/ b = getJoin (Join a <> Join b)
{-# INLINE (\/) #-}

-- @ 'join' :: 'Lattice' a => 'Minimal' a => 'Set' a -> a @
--
join :: (Join-Monoid) a => Lattice a => Foldable f => f a -> a
join = joinWith id

-- | The join of a list of join-semilattice elements (of length at least top)
join1 :: Lattice a => Foldable1 f => f a -> a
join1 = joinWith1 id

-- >>> joinWith Just [1..5 :: Int]
-- Just 5
-- >>> joinWith N5 [1,5,0/0]
-- N5 {fromN5 = Infinity}
-- >>> joinWith MaxMin $ [IntSet.fromList [1..5], IntSet.fromList [2..4]]
-- MaxMin {unMaxMin = fromList [2,3,4]}
joinWith :: (Join-Monoid) a => Foldable t => (b -> a) -> t b -> a
joinWith f = foldl' (\x y -> x \/ f y) bottom
{-# INLINE joinWith #-}

-- | Fold over a non-empty collection using the join operation of an arbitrary join semilattice.
--
joinWith1 :: Foldable1 t => (Join-Semilattice) a => (b -> a) -> t b -> a
joinWith1 f = getJoin . foldMap1 (Join . f)
{-# INLINE joinWith1 #-}

-- | Lower set in /b/ generated by an element in /a/.
--
-- indexLower
lower :: Ideal a b => a -> b -> Bool
lower i a = connr connection a `joinLe` i

infix 4 `joinLe`
-- | The partial ordering induced by the join-semilattice structure.
--
--
-- Normally when /a/ implements 'Ord' we should have:
-- @ 'joinLe' x y ≡ x '<=' y @
--
joinLe :: Eq a => (Join-Semilattice) a => a -> a -> Bool
joinLe x y = x \/ y == y

infix 4 `joinGe`
-- | The partial ordering induced by the join-semilattice structure.
--
-- Normally when /a/ implements 'Ord' we should have:
-- @ 'joinGe' x y ≡ x '>=' y @
--
joinGe :: Eq a => (Join-Semilattice) a => a -> a -> Bool
joinGe x y = x \/ y == x

-- | Partial version of 'Data.Ord.compare'.
--
-- Normally when /a/ implements 'Prd' we should have:
-- @ 'pcompareJoin' x y ≡ 'pcompare' x y @
--
pcompareJoin :: Eq a => (Join-Semilattice) a => a -> a -> Maybe Ordering
pcompareJoin x y
  | x == y = Just EQ
  | x \/ y == y && x /= y = Just LT
  | x \/ y == x && x /= y = Just GT
  | otherwise = Nothing


-------------------------------------------------------------------------------
-- Meet semilattices
-------------------------------------------------------------------------------



newtype Meet a = Meet { getMeet :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative Meet where
    pure = Meet
    Meet f <*> Meet a = Meet (f a)

{-
instance (Eq a, Semigroup (Meet a)) => Prd (Meet a) where
    (<=) x y = x <> y == x
    (>=) x y = x <> y == y
    pcompare x y | x == y = Just EQ
		 | x <> y == x && x /= y = Just LT
		 | x <> y == y && x /= y = Just GT
		 | otherwise = Nothing

instance (Eq a, Monoid (Meet a)) => Maximal (Meet a) where
    maximal = mempty
-}

-- Minimal (Join a) => Minimal (Down (Meet a))

top :: (Meet-Monoid) a => a
top = getMeet mempty
{-# INLINE top #-}

infixr 6 /\ -- comment for the parser

-- | Meet operation on a semilattice.
--
-- >>> (> (0::Int)) /\ ((< 10) ∨ (== 15)) $ 15
-- True
--
(/\) :: (Meet-Semilattice) a => a -> a -> a
a /\ b = getMeet (Meet a <> Meet b)
{-# INLINE (/\) #-}

meet :: Foldable f => (Meet-Monoid) a => Lattice a => f a -> a
meet = meetWith id

-- | The meet of a non-empty collection of meet-semilattice elements.
meet1 :: Foldable1 f => Lattice a => f a -> a
meet1 = meetWith1 id

-- | Fold over a collection using the multiplicative operation of an arbitrary semiring.
-- 
-- @
-- 'meet' f = 'Data.foldr'' ((*) . f) 'top'
-- @
--
--
-- >>> meetWith Just [1..5 :: Int]
-- Just 1
-- >>> meetWith N5 [1,5,0/0]
-- N5 {fromN5 = -Infinity}
meetWith :: Foldable f => (Meet-Monoid) a => (b -> a) -> f b -> a
meetWith f = foldl' (\x y -> x /\ f y) top
{-# INLINE meetWith #-}

-- | Fold over a non-empty collection using the multiplicative operation of a semiring.
--
-- As the collection is non-empty this does not require a distinct multiplicative unit:
--
-- >>> meetWith1 Just $ 1 :| [2..5 :: Int]
-- Just 120
-- >>> meetWith1 First $ 1 :| [2..(5 :: Int)]
-- First {getFirst = 15}
-- >>> meetWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Just 11}
--
meetWith1 :: Foldable1 f => (Meet-Semilattice) a => (b -> a) -> f b -> a
meetWith1 f = getMeet . foldMap1 (Meet . f)
{-# INLINE meetWith1 #-}

-- | Upper set in /a/ generated by an element in /b/.
upper :: Filter a b => a -> b -> Bool
upper a b = connl connection a `meetGe` b



infix 4 `meetLe`
-- | The partial ordering induced by the meet-semilattice structure.
--
-- Normally when /a/ implements 'Prd' we should have:
-- @ 'meetLe' x y ≡ x '<=' y @
--
meetLe :: Eq a => (Meet-Semilattice) a => a -> a -> Bool
meetLe x y = let z = x /\ y in if z /= z && x /= x then True else z == x

infix 4 `meetGe`
-- | The partial ordering induced by the meet-semilattice structure.
--
-- Normally when /a/ implements 'Prd' we should have:
-- @ 'meetGe' x y ≡ x '>=' y @
--
meetGe :: Eq a => (Meet-Semilattice) a => a -> a -> Bool
meetGe x y = x /\ y == y

-- | Partial version of 'Data.Ord.compare'.
--
-- Normally when /a/ implements 'Prd' we should have:
-- @ 'pcompareJoin' x y ≡ 'pcompare' x y @
--
pcompareMeet :: Eq a => (Meet-Semilattice) a => a -> a -> Maybe Ordering
pcompareMeet x y
  | x == y = Just EQ
  | x /\ y == x && x /= y = Just LT
  | x /\ y == y && x /= y = Just GT
  | otherwise = Nothing


-------------------------------------------------------------------------------
-- Lattices
-------------------------------------------------------------------------------

type LatticeLaw a = ((Join-Semilattice) a, (Meet-Semilattice) a)


-- | Lattices.
--
-- A lattice is a partially ordered set in which every two elements have a unique join 
-- (least upper bound or supremum) and a unique meet (greatest lower bound or infimum). 
--
-- /Associativity/
--
-- @
-- x '\/' (y '\/' z) = (x '\/' y) '\/' z
-- x '/\' (y '/\' z) = (x '/\' y) '/\' z
-- @
--
-- /Commutativity/
--
-- @
-- x '\/' y = y '\/' x
-- x '/\' y = y '/\' x
-- @
--
-- /Idempotency/
--
-- @
-- x '\/' x = x
-- x '/\' x = x
-- @
--
-- /Absorption/
--
-- @
-- (x '\/' y) '/\' y = y
-- (x '/\' y) '\/' y = y
-- @
--
-- See <http://en.wikipedia.org/wiki/Lattice_(order)> and <http://en.wikipedia.org/wiki/Absorption_law>.
--
-- Note that distributivity is _not_ a requirement for a lattice,
-- however distributive lattices are idempotent, commutative dioids.
-- 
class LatticeLaw a => Lattice a where

    -- | Reduce a free lattice expression:
    -- 
    -- > (a11 /\ ... /\ a1m) \/ (a21 /\ ... /\ a2n) \/ ...
    --
    reduce1 :: (Foldable1 f, Functor f) => f (f a) -> a
    reduce1 = join1 . fmap meet1
    {-# INLINE reduce1 #-}

    infix 4 <~, >~, ?~, ~~, /~, `pcompare`

    -- | Non-strict partial order relation on /a/.
    --
    -- '<~' is reflexive, anti-symmetric, and transitive.
    --
    (<~) :: Eq a => a -> a -> Bool
    (<~) = meetLe

    -- | Converse non-strict partial order relation on /a/.
    --
    -- '>~' is reflexive, anti-symmetric, and transitive.
    --
    (>~) :: Eq a => a -> a -> Bool
    (>~) = flip (<~)

    -- | Comparability relation on /a/. 
    --
    -- '?~' is reflexive, symmetric, and transitive.
    --
    -- If /a/ implements 'Ord' then (ideally) @x ?~ y = True@.
    --
    (?~) :: Eq a => a -> a -> Bool
    x ?~ y = x <~ y || x >~ y

    -- | Similarity relation on /a/. 
    --
    -- '~~' is reflexive and symmetric, but not necessarily transitive.
    --
    -- Note this is only equivalent to '==' in a total (i.e. linear) order:
    --
    -- > (0/0 :: Float) ~~ 5 = True
    --
    (~~) :: Eq a => a -> a -> Bool
    x ~~ y = not (x `lt` y) && not (x `gt` y)

    -- | Negation of '~~'.
    --
    (/~) :: Eq a => a -> a -> Bool
    x /~ y = not $ x ~~ y

    -- | A partial version of 'Data.Ord.compare'.
    --
    -- > x <~ y = maybe False (<= EQ) (pcompare x y)
    -- > x == y = maybe False (== EQ) (pcompare x y)
    -- > x >~ y = maybe False (>= EQ) (pcompare x y)
    -- > x ?~ y = maybe False (const True) (pcompare x y)
    --
    pcompare :: Eq a => a -> a -> Maybe Ordering
    pcompare x y 
      | x <~ y    = Just $ if y <~ x then EQ else LT
      | y <~ x    = Just GT
      | otherwise = Nothing

infix 4 `eq`, `ne`, `lt`, `gt`, `pmax`, `pmin`

-- | Equivalence relation on /a/.
--
-- 'eq' is reflexive, symmetric, and transitive.
--
-- > lt x y = maybe False (== EQ) (pcompare x y)
--
-- Use this as a lawful substitute for '==' when comparing
-- floats or doubles.
--
-- If /a/ implements 'Eq' then ideally @'eq' = ('==')@.
--
eq :: (Lattice a, Eq a) => a -> a -> Bool
eq x y = x <~ y && x >~ y

ne :: (Lattice a, Eq a) => a -> a -> Bool
ne x y = not (eq x y)

-- | Strict partial order relation on /a/.
--
-- 'lt' is irreflexive, asymmetric, and transitive.
--
-- > lt x y = maybe False (< EQ) (pcompare x y)
--
-- If /a/ implements 'Ord' then ideally @x `lt` y = x < y@.
--
lt :: (Lattice a, Eq a) => a -> a -> Bool
lt x y = x <~ y && x `ne` y

-- | Converse strict partial order relation on /a/.
--
-- 'gt' is irreflexive, asymmetric, and transitive.
--
-- > gt x y = maybe False (> EQ) (pcompare x y)
--
-- If /a/ implements 'Ord' then ideally @x `gt` y = x > y@.
--
gt :: (Lattice a, Eq a) => a -> a -> Bool
gt x y = x >~ y && x `ne` y

-- | A partial version of 'Data.Ord.max'. 
--
-- Default instance returns the connr argument in the case of equality.
--
pmax :: (Lattice a, Eq a) => a -> a -> Maybe a
pmax x y = do
  o <- pcompare x y
  case o of
    GT -> Just x
    EQ -> Just y
    LT -> Just y

-- | A partial version of 'Data.Ord.min'. 
--
-- Default instance returns the connr argument in the case of equality.
--
pmin :: (Lattice a, Eq a) => a -> a -> Maybe a
pmin x y = do
  o <- pcompare x y
  case o of
    GT -> Just y
    EQ -> Just x
    LT -> Just x

-- | Greatest lower bound operator.
--
-- If the lattice is distributive then 'glb' has the following properties.
--
-- @ 
-- 'glb' x y y = y
-- 'glb' x y z = 'glb' z x y
-- 'glb' x y z = 'glb' x z y
-- 'glb' ('glb' x w y) w z = 'glb' x w ('glb' y w z)
-- @
--
-- >>> glb 1.0 9.0 7.0
-- 7.0
-- >>> glb 1.0 9.0 (0.0 / 0.0)
-- 9.0
-- >>> glb (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: Set Int
-- fromList [3,5]
--
-- See Birkhoff's self-dual < https://en.wikipedia.org/wiki/Median_algebra ternary median > operation.
--
glb :: Lattice a => a -> a -> a -> a
glb x y z = (x \/ y) /\ (y \/ z) /\ (z \/ x)

-- | Least upper bound operator.
--
-- The order dual of 'glb'.
--
-- >>> lub 1.0 9.0 7.0
-- 7.0
-- >>> lub 1.0 9.0 (0.0 / 0.0)
-- 1.0
--
lub :: Lattice a => a -> a -> a -> a
lub x y z = (x /\ y) \/ (y /\ z) \/ (z /\ x)

-------------------------------------------------------------------------------
-- Bounded lattices
-------------------------------------------------------------------------------

type BoundedLatticeLaw a = (Lattice a, (Join-Monoid) a, (Meet-Monoid) a)

--type LowerBoundedLattice a = (Lattice a, (Join-Monoid) a)

--type UpperBoundedLattice a = (Lattice a, (Meet-Monoid) a)

-- | Bounded lattices.
--
-- A bounded lattice is a lattice with two neutral elements wrt join and meet
-- operations:
--
-- /Neutrality/
--
-- @
-- x '\/' 'bottom' = x
-- x '/\' 'top' = x
-- @
--
class BoundedLatticeLaw a => BoundedLattice a where

    -- | Reduce a free bounded lattice expression.
    -- 
    -- >>> reduce [[1, 2], [3, 4 :: Int]] -- 1 /\ 2 \/ 3 /\ 4
    -- 3
    -- >>> reduce $ sequence [[1, 2], [3, 4 :: Int]] -- (1 \/ 2) /\ (3 \/ 4)
    -- 2
    --
    reduce :: (Foldable f, Functor f) => f (f a) -> a
    reduce = join . fmap meet
    {-# INLINE reduce #-}

-------------------------------------------------------------------------------
-- Heyting algebras
-------------------------------------------------------------------------------

type HeytingLaw a = (BoundedLattice a, (Meet-Quantale) a)

prop_residuated :: (Heyting a, Eq a) => a -> a -> a -> Bool
prop_residuated x y z = x /\ y <~ z `iff` y <~ (x ==> z) `iff` x <~ (z <== y)

-- | A Heyting algebra is a bounded lattice equipped with an implication operation.
--
-- /Laws/
--
-- @
-- x '==>' x           = 'top'
-- x '/\' (x '==>' y)  = x '/\' y
-- y '/\' (x '==>' y)  = y
-- x '==>' (y '/\' z)  = (x '==>' y) '/\' (x '==>' z)
-- x '==>' (y '==>' z) = (x '/\' y) '==>' z
-- 'not' (x '/\' y)    = 'not' (x '\/' y)
-- 'not' (x '\/' y)    = 'not' x '/\' 'not' y
-- @
--
-- 
-- > x '/\' y '<~' z `iff` x '<~' (y '==>' z)
-- > (x '==>' y) '\/' x '<=' y
-- > y '<~' x '==>' x '/\' y
-- > x '<~' y `iff` x '==>' y = 'top'
-- > x '<~' y => z '==>' x '<~' z '==>' y
-- > x '<~' y => x '==>' z '<~' y '==>' z
--
-- All this means that @x '==>' y@ is an [exponential object](https://ncatlab.org/nlab/show/exptopntial%2Bobject),
-- which makes any Heyting algebra a [cartesian closed category](https://ncatlab.org/nlab/show/cartesian%2Bclosed%2Bcategory).
--
class HeytingLaw a => Heyting a where

   
    -- | 
    -- > not x = x ==> bottom
    -- > not @Bool = Prelude.not
    --
    -- Note that Heyting algebras needn't obey the law of the excluded middle:
    --
    -- > EQ \/ not EQ = EQ \/ (EQ ==> LT) = EQ \/ LT = EQ
    --
    not :: a -> a
    not x = x ==> bottom

    infixr 2 `iff`
    iff :: a -> a -> a
    iff x y = x ==> y /\ y ==> x

    infixr 3 `xor`
    xor :: a -> a -> a
    xor x y = (x \/ y) /\ not (x /\ y)


infixr 3 ==>

{-| Logical implication.

    The laws are the same as those of a unital 'Data.Semigroup.Quantale':
@
x '==>' x           = 'top'
x '==>' (y '==>' z) = (x '/\' y) '==>' z (currying)
@

@
x '/\' (x '==>' y)  = x '/\' y
y '/\' (x '==>' y)  = y
x '==>' (y '/\' z)  = (x '==>' y) '/\' (x '==>' z)
@
-}
(==>) :: (Meet-Quantale) a => a -> a -> a
(==>) x y = getMeet $ Meet x \\ Meet y

infixl 3 <==

(<==) :: (Meet-Quantale) a => a -> a -> a
(<==) x y = getMeet $ Meet x // Meet y

infixr 3 `xor3`
xor3 :: Heyting a => a -> a -> a -> a
xor3 x y z = (x `xor` y `xor` z) /\ not (x /\ y /\ z)


instance Heyting Bool where
  not = P.not

instance Heyting Ordering where
  not LT = GT
  not _ = LT

---------------------------------------------------------------------
-- DerivingVia
---------------------------------------------------------------------

newtype F1 (f :: Type -> Type) a = F1 (f a) deriving stock (Eq, Ord, Show, Functor)

instance (Applicative f, Semigroup a) => Semigroup (F1 f a) where
  F1 x <> F1 y = F1 $ (<>) <$> x <*> y 

instance (Applicative f, Monoid a) => Monoid (F1 f a) where
  mempty = F1 $ pure mempty

instance (Applicative f, Group a) => Group (F1 f a) where
  invert (F1 x) = F1 $ fmap invert x

instance (Applicative f, Quantale a) => Quantale (F1 f a) where
  F1 x // F1 y = F1 $ (//) <$> x <*> y 
  (\\) = flip (//)

newtype F2 (f :: Type -> Type) (g :: Type -> Type) a = F2 (f (g a)) deriving stock (Eq, Ord, Show, Functor)
deriving via (Compose (f :: Type -> Type) (g :: Type -> Type)) instance (Applicative f, Applicative g) => Applicative (F2 f g) 

instance (Applicative f, Applicative g, Semigroup a) => Semigroup (F2 f g a) where
  (<>) = liftA2 (<>)

instance (Applicative f, Applicative g, Monoid a) => Monoid (F2 f g a) where
  mempty = pure mempty

instance (Applicative f, Applicative g, Group a) => Group (F2 f g a) where
  invert = fmap invert

-- N5 lattice ordering: NInf <= NaN <= PInf
le :: (Ord a, Fractional a) => a -> a -> Bool
le x y | x /= x && y /= y = True
       | x /= x = y == 1/0
       | y /= y = x == -1/0
       | otherwise = x P.<= y

newtype PMin a = PMin a deriving stock (Eq, Ord, Show, Functor)

instance (Ord a, Fractional a) => Semigroup (PMin a) where
  PMin x <> PMin y = PMin $ if le x y then x else y

instance (Ord a, Fractional a) => Monoid (PMin a) where
  mempty = PMin $ 1/0


newtype PMax a = PMax a deriving stock (Eq, Ord, Show, Functor)

instance (Ord a, Fractional a) => Semigroup (PMax a) where
  PMax x <> PMax y = PMax $ if le x y then y else x

instance (Ord a, Fractional a) => Monoid (PMax a) where
  mempty = PMax $ -1/0


---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------


deriving via (F1 Join (Max ())) instance Semigroup (Join ())
deriving via (F1 Join (Max ())) instance Monoid (Join ())
deriving via (F1 Meet (Min ())) instance Semigroup (Meet ())
deriving via (F1 Meet (Min ())) instance Monoid (Meet ())
instance Lattice ()
instance BoundedLattice ()

deriving via (F1 Join Any) instance Semigroup (Join Bool)
deriving via (F1 Join Any) instance Monoid (Join Bool)
deriving via (F1 Meet All) instance Semigroup (Meet Bool)
deriving via (F1 Meet All) instance Monoid (Meet Bool)
instance Lattice Bool
instance BoundedLattice Bool

instance Quantale (Meet Bool) where
  (\\) = liftA2 (<=)
  (//) = flip (\\)




deriving via (F1 Join (Max Word8)) instance Semigroup (Join Word8)
deriving via (F1 Join (Max Word8)) instance Monoid (Join Word8)
deriving via (F1 Meet (Min Word8)) instance Semigroup (Meet Word8)
deriving via (F1 Meet (Min Word8)) instance Monoid (Meet Word8)
--deriving via (F1 Meet (Sum Word8)) instance Quantale (Meet Word8)
instance Lattice Word8
instance BoundedLattice Word8



deriving via (F1 Join (PMax Float)) instance Semigroup (Join Float)
deriving via (F1 Join (PMax Float)) instance Monoid (Join Float)
deriving via (F1 Meet (PMin Float)) instance Semigroup (Meet Float)
deriving via (F1 Meet (PMin Float)) instance Monoid (Meet Float)
instance Lattice Float
instance BoundedLattice Float

deriving via (F1 Join (PMax Double)) instance Semigroup (Join Double)
deriving via (F1 Join (PMax Double)) instance Monoid (Join Double)
deriving via (F1 Meet (PMin Double)) instance Semigroup (Meet Double)
deriving via (F1 Meet (PMin Double)) instance Monoid (Meet Double)
instance Lattice Double
instance BoundedLattice Double

deriving via (F1 Join (r -> Join a)) instance Semigroup (Join a) => Semigroup (Join (r -> a))
deriving via (F1 Join (r -> Join a)) instance Monoid (Join a) => Monoid (Join (r -> a))
deriving via (F1 Meet (r -> Meet a)) instance Semigroup (Meet a) => Semigroup (Meet (r -> a))
deriving via (F1 Meet (r -> Meet a)) instance Monoid (Meet a) => Monoid (Meet (r -> a))
--deriving via (F1 Meet (r -> a)) instance Quantale a => Quantale (Meet (r -> a))
instance Lattice a => Lattice (r -> a)
instance BoundedLattice a => BoundedLattice (r -> a)




-- compare with Sign dioid
joinOrdering :: Ordering -> Ordering -> Ordering
joinOrdering LT x = x
joinOrdering x LT = x
joinOrdering EQ GT = GT
joinOrdering EQ _  = EQ
joinOrdering GT _  = GT

meetOrdering :: Ordering -> Ordering -> Ordering
meetOrdering LT _ = LT
meetOrdering _ LT = LT
meetOrdering EQ _  = EQ
meetOrdering _ EQ  = EQ
meetOrdering GT GT = GT

impliesOrdering :: Ordering -> Ordering -> Ordering
impliesOrdering LT _ = GT
impliesOrdering EQ LT = LT
impliesOrdering EQ _ = GT
impliesOrdering GT x = x

instance Semigroup (Join Ordering) where
  (<>) = liftA2 joinOrdering
  {-# INLINE (<>) #-}

instance Monoid (Join Ordering) where
  mempty = pure GT
  {-# INLINE mempty #-}

instance Semigroup (Meet Ordering) where
  (<>) = liftA2 meetOrdering
  {-# INLINE (<>) #-}

instance Monoid (Meet Ordering) where
  mempty = pure GT
  {-# INLINE mempty #-}

instance Quantale (Meet Ordering) where
  (\\) = liftA2 impliesOrdering 
  -- (\\) = liftA2 $ \x y -> negOrdering x \/ y
  (//) = flip (\\)

instance Lattice Ordering
instance BoundedLattice Ordering




--instance Lattice a => BoundedLattice (Bounded a) where

{-



-- Lattices
instance Lattice ()
instance Lattice Word
instance Lattice Word8
instance Lattice Word16
instance Lattice Word32
instance Lattice Word64
instance Lattice Natural

instance Lattice Int
instance Lattice Int8
instance Lattice Int16
instance Lattice Int32
instance Lattice Int64
instance Lattice Integer

instance Lattice Uni
instance Lattice Deci
instance Lattice Centi
instance Lattice Milli
instance Lattice Micro
instance Lattice Nano
instance Lattice Pico

instance Lattice a => Lattice (Down a)
instance (Lattice a, Lattice b) => Lattice (Either a b)
instance Lattice a => Lattice (Maybe a)
instance Lattice a => Lattice (IntMap.IntMap a)
instance Lattice IntSet.IntSet
instance Ord a => Lattice (Set.Set a)
instance (Ord k, Lattice a) => Lattice (Map.Map k a)
-}

---------------------------------------------------------------------
-- Semigroup Instances
---------------------------------------------------------------------




-- >>> Down True \/ Down False
-- Down False
instance (Meet-Semigroup) a => Semigroup (Join (Down a)) where
  (<>) = liftA2 . liftA2 $ (/\) 

-- >>> bottom :: Down Bool
-- Down True
instance (Meet-Monoid) a => Monoid (Join (Down a)) where
  mempty = pure . pure $ top

-- >>> Down True /\ Down False
-- Down True
instance (Join-Semigroup) a => Semigroup (Meet (Down a)) where
  (<>) = liftA2 . liftA2 $ (\/) 

-- >>> top :: Down Bool
-- Down False
instance (Join-Monoid) a => Monoid (Meet (Down a)) where
  mempty = pure . pure $ bottom


instance Semigroup (Max a) => Semigroup (Join (Max a)) where
  (<>) = liftA2 (<>)


{-
instance Ord a => Semigroup (Join (Down a)) where
  (<>) = liftA2 . liftA2 $ (\/)

instance (Join-Monoid) a => Monoid (Join (Down a)) where
  mempty = pure . pure $ bottom
-}
instance (Join-Semigroup) a => Semigroup (Join (Maybe a)) where
  Join (Just x) <> Join (Just y) = Join . Just $ x \/ y
  Join (x@Just{}) <> _           = Join x
  Join Nothing  <> y             = y

instance (Join-Semigroup) a => Monoid (Join (Maybe a)) where
  mempty = Join Nothing


instance (Meet-Semigroup) a => Semigroup (Meet (Maybe a)) where
  Meet Nothing  <> _             = Meet Nothing
  Meet (Just{}) <> Meet Nothing  = Meet Nothing
  Meet (Just x) <> Meet (Just y) = Meet . Just $ x /\ y

  -- Mul a <> Mul b = Mul $ liftA2 (/\) a b

instance (Meet-Monoid) a => Monoid (Meet (Maybe a)) where
  mempty = Meet $ pure top

instance Lattice a => Lattice (Maybe a)
instance (Lattice a, (Meet-Monoid) a) => BoundedLattice (Maybe a)

--TODO derivingVia
x /// y = getMeet $ Meet x // Meet y

x \\\ y = getMeet $ Meet x \\ Meet y

--TODO remove Eq constraint?
instance (Eq a, (Meet-Quantale) a) => Quantale (Meet (Maybe a)) where
  (\\) = liftA2 (\\\)
  (//) = liftA2 (///)

{-
instance (Eq a, Heyting a, (Meet-Monoid) a) => Heyting (Maybe a) where
  Just a  ==> Just b = Just $ a ==> b
  Nothing ==> _        = Just top
  _       ==> Nothing  = Nothing
-}



joinEither :: ((Join-Semilattice) a, (Join-Semilattice) b) => Either a b -> Either a b -> Either a b
joinEither (Right x) (Right y) = Right (x \/ y)
joinEither u@(Right _) _ = u
joinEither _ u@(Right _) = u
joinEither (Left x) (Left y) = Left (x \/ y)

instance (Semigroup (Join a), Semigroup (Join b)) => Semigroup (Join (Either a b)) where
  (<>) = liftA2 joinEither

instance (Monoid (Join a), Semigroup (Join b)) => Monoid (Join (Either a b)) where
  mempty = pure $ Left bottom


meetEither :: ((Meet-Semilattice) a, (Meet-Semilattice) b) => Either a b -> Either a b -> Either a b
meetEither (Left x) (Left y) = Left (x /\ y)
meetEither l@(Left _) _ = l
meetEither _ l@(Left _) = l
meetEither (Right x) (Right y) = Right (x /\ y)

instance (Semigroup (Meet a), Semigroup (Meet b)) => Semigroup (Meet (Either a b)) where
  (<>) = liftA2 meetEither

instance (Semigroup (Meet a), Monoid (Meet b)) => Monoid (Meet (Either a b)) where
  mempty = pure $ Right top

-- | All minimal elements of the upper lattice cover all maximal elements of the lower lattice.
instance (Lattice a, Lattice b) => Lattice (Either a b)
instance (BoundedLattice a, BoundedLattice b) => BoundedLattice (Either a b)


{-

instance (Join-Semigroup) (Max a) => Semigroup (Additive (Max a)) where
  (<>) = liftA2 (\/)

instance (Join-Monoid) (Max a) => Monoid (Additive (Max a)) where
  mempty = pure bottom

-- workaround for poorly specified entailment: instance (Ord a, Bounded a) => Monoid (Max a)
instance (Minimal a, Semigroup (Max a)) => Monoid (Join (Max a)) where
  mempty = pure $ Max minimal

instance (Join-Semigroup) a => Semigroup (Join (Dual a)) where
  (<>) = liftA2 . liftA2 $ flip (\/)

instance (Join-Monoid) a => Monoid (Join (Dual a)) where
  mempty = pure . pure $ bottom


instance (Join-Semigroup) a => Semigroup (Join (Down a)) where
  (<>) = liftA2 . liftA2 $ (\/) 

instance (Join-Monoid) a => Monoid (Join (Down a)) where
  --Join (Down a) <> Join (Down b)
  mempty = pure . pure $ bottom

instance Semigroup (Max a) => Semigroup (Join (Max a)) where
  (<>) = liftA2 (<>)

-- MinPlus Predioid
-- >>> Min 1  `mul`  Min 2 :: Min Int
-- Min {getMin = 3}
instance (Join-Semigroup) a => Semigroup (Multiplicative (Min a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 (\/) a b

-- MinPlus Dioid
instance (Join-Monoid) a => Monoid (Multiplicative (Min a)) where
  mempty = Multiplicative $ pure bottom

--instance ((Meet-Semigroup) a, Maximal a) => Monoid (Meet a) where
--  mempty = Meet maximal

-- >>> Min 1 /\ Min 2 :: Min Int
-- Min {getMin = 1}
instance Semigroup (Min a) => Semigroup (Meet (Min a)) where
  (<>) = liftA2 (<>)

instance (Meet-Semigroup) (Min a) => Semigroup (Additive (Min a)) where
  (<>) = liftA2 (/\) 

instance (Meet-Monoid) (Min a) => Monoid (Additive (Min a)) where
  mempty = pure top

-- workaround for poorly specified entailment: instance (Ord a, Bounded a) => Monoid (Min a)
-- >>> bottom :: Min Natural
-- Min {getMin = 0}
instance (Maximal a, Semigroup (Min a)) => Monoid (Meet (Min a)) where
  mempty = pure $ Min maximal

-- MaxTimes Predioid

instance (Meet-Semigroup) a => Semigroup (Meet (Max a)) where
  Meet a <> Meet b = Meet $ liftA2 (/\) a b

-- MaxTimes Dioid
instance (Meet-Monoid) a => Monoid (Meet (Max a)) where
  mempty = Meet $ pure top




-}

--instance ((Join-Semigroup) a, Minimal a) => Monoid (Join a) where
--  mempty = Join minimal

-- instance (Meet-Monoid) (Down a) => Monoid (Meet (Down a)) where mempty = Down <$> mempty

instance ((Join-Semigroup) a, (Join-Semigroup) b) => Semigroup (Join (a, b)) where
  Join (x1, y1) <> Join (x2, y2) = Join (x1 \/ x2, y1 \/ y2)


instance Ord a => Semigroup (Join (Set.Set a)) where
  (<>) = liftA2 Set.union 

instance Ord a => Monoid (Join (Set.Set a)) where
  mempty = Join Set.empty

instance Ord a => Semigroup (Meet (Set.Set a)) where
  (<>) = liftA2 Set.intersection 

instance (Ord a, Finite a) => Monoid (Meet (Set.Set a)) where
  mempty = Meet $ Set.fromList universeF

instance Ord a => Lattice (Set.Set a)
instance (Ord a, Finite a) => BoundedLattice (Set.Set a)

instance Ord a => Quantale (Meet (Set.Set a)) where
    (\\) = liftA2 (Set.\\)
    (//) = flip (\\)


-- |
-- Power set: the canonical example of a Boolean algebra
instance (Ord a, Finite a) => Heyting (Set a) where
  --not a = Set.fromList universe `Set.difference` a
  not = Set.difference top
  iff x y = Set.fromList
      [ z
      | z <- universeF
      , Set.member z x `iff` Set.member z y
      ]

{-
import safe qualified Data.Map.Merge.Lazy as Merge
instance (Ord a, Finite a) => Quantale (Set.Set a) where
    x // y = Set.union (complement x) y
    (\\) = flip (//)

-- |
-- It is not a boolean algebra (even if values are).
instance (Ord k, Finite k, UnitalQuantale v) => Quantale (Map.Map k v) where
  a \\ b = Map.union x y where
    x = Merge.merge
      Merge.dropMissing                    -- drop if an element is missing in @b@
      (Merge.mapMissing (\_ _ -> mempty))     -- put @top@ if an element is missing in @a@
      (Merge.zipWithMatched (\_ -> (\\))) -- merge  matching elements with @==>@
      a b

    y = Map.fromList [(k, mempty) | k <- universeF, not (Map.member k a), not (Map.member k b) ]
                            -- for elements which are not in a, nor in b add
                            -- a @top@ key
-}

complement :: (Ord a, Finite a) => Set.Set a -> Set.Set a
complement xs = Set.fromList [ x | x <- universeF, Set.notMember x xs]



instance (Ord k, (Join-Semigroup) a) => Semigroup (Join (Map.Map k a)) where
  (<>) = liftA2 (Map.unionWith (\/))

instance (Join-Semigroup) a => Semigroup (Join (IntMap.IntMap a)) where
  (<>) = liftA2 (IntMap.unionWith (\/))

instance Semigroup (Join IntSet.IntSet) where
  (<>) = liftA2 IntSet.union 

instance Monoid (Join IntSet.IntSet) where
  mempty = Join IntSet.empty

instance (Join-Semigroup) a => Monoid (Join (IntMap.IntMap a)) where
  mempty = Join IntMap.empty



instance (Ord k, (Join-Semigroup) a) => Monoid (Join (Map.Map k a)) where
  mempty = Join Map.empty


instance ((Meet-Semigroup) a, (Meet-Semigroup) b) => Semigroup (Meet (a, b)) where
  Meet (x1, y1) <> Meet (x2, y2) = Meet (x1 /\ x2, y1 /\ y2)



instance (Ord k, (Meet-Semigroup) a) => Semigroup (Meet (Map.Map k a)) where
  (<>) = liftA2 (Map.intersectionWith (/\))

instance (Meet-Semigroup) a => Semigroup (Meet (IntMap.IntMap a)) where
  (<>) = liftA2 (IntMap.intersectionWith (/\))

instance Semigroup (Meet IntSet.IntSet) where
  (<>) = liftA2 IntSet.intersection 

{-
instance (Ord k, (Meet-Monoid) k, (Meet-Monoid) a) => Monoid (Meet (Map.Map k a)) where
  mempty = Meet $ Map.singleton top top

instance (Meet-Monoid) a => Monoid (Meet (IntMap.IntMap a)) where
  mempty = Meet $ IntMap.singleton 0 top --TODO check
-}

{-


instance Monoid a => Semiring (Seq.Seq a) where
  (*) = liftA2 (<>)
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ Seq.singleton mempty

instance (Ord k, Monoid k, Monoid a) => Semiring (Map.Map k a) where
  xs * ys = foldMap (flip Map.map xs . (<>)) ys
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ Map.singleton mempty mempty

instance Monoid a => Semiring (IntMap.IntMap a) where
  xs * ys = foldMap (flip IntMap.map xs . (<>)) ys
  {-# INLINE (*) #-}

  fromBoolean = fromBooleanDef $ IntMap.singleton 0 mempty
-}



{-
#define deriveJoinSemigroup(ty)             \
instance Semigroup (Join ty) where {        \
   a <> b = (P.max) <$> a <*> b             \
;  {-# INLINE (<>) #-}                      \
}

deriveJoinSemigroup(())
deriveJoinSemigroup(Bool)

deriveJoinSemigroup(Int)
deriveJoinSemigroup(Int8)
deriveJoinSemigroup(Int16)
deriveJoinSemigroup(Int32)
deriveJoinSemigroup(Int64)
deriveJoinSemigroup(Integer)

deriveJoinSemigroup(Word)
deriveJoinSemigroup(Word8)
deriveJoinSemigroup(Word16)
deriveJoinSemigroup(Word32)
deriveJoinSemigroup(Word64)
deriveJoinSemigroup(Natural)

deriveJoinSemigroup(Uni)
deriveJoinSemigroup(Deci)
deriveJoinSemigroup(Centi)
deriveJoinSemigroup(Milli)
deriveJoinSemigroup(Micro)
deriveJoinSemigroup(Nano)
deriveJoinSemigroup(Pico)


#define deriveJoinMonoid(ty)                \
instance Monoid (Join ty) where {           \
   mempty = pure minimal                    \
;  {-# INLINE mempty #-}                    \
}

deriveJoinMonoid(())
deriveJoinMonoid(Bool)

deriveJoinMonoid(Int)
deriveJoinMonoid(Int8)
deriveJoinMonoid(Int16)
deriveJoinMonoid(Int32)
deriveJoinMonoid(Int64)

deriveJoinMonoid(Word)
deriveJoinMonoid(Word8)
deriveJoinMonoid(Word16)
deriveJoinMonoid(Word32)
deriveJoinMonoid(Word64)
deriveJoinMonoid(Natural)
-}
