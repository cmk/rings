{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE Rank2Types #-}

module Data.Ring.Index where

import Data.Int
import Data.Word
import Data.Prd
import Data.Prd.Nan
import Data.Prd.Lattice
import Data.Bifunctor
import Data.Dioid.Interval
import Data.Function
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Connection
import Data.Connection.Int
import Data.Connection.Word
import Data.Connection.Float
import Data.Foldable
import Data.List (unfoldr)
import GHC.Num (subtract)
import Numeric.Natural
import Data.Bool
import Prelude hiding (Enum(..), Ord(..), until)

import Orphans ()
import Control.Monad.Loops
import Control.Monad.State

import Data.MemoCombinators (Memo)
import Data.MemoCombinators.Class
import qualified Data.MemoCombinators as Memo
import qualified Control.Category as C



-- https://en.wikipedia.org/wiki/Filter_(mathematics)
-- https://en.wikipedia.org/wiki/Ideal_(order_theory)

{-
a subset I of a lattice (P,≤) is an ideal if and only if 
- it is a lower set that is closed under finite joins (suprema), i.e., it is nonempty and for all x, y in I, the element x \vee y of P is also in I.

properties
- Rep a is upward-closed:
  - up x s && x <~ y ==> up y s
  - up x s && up y s ==> connl filter x /\ connl filter y >~ s
- Rep a is downward-closed:
  - dn x s && x >~ y ==> dn y s
  - dn x s && dn y s ==> connl ideal x \/ connl ideal y ~< s

dn x y == up (Down x) (Down y)
dn (Down x) (Down y) == up x y

Conn a a
filter >>> ideal

Conn (Rep a) (Rep a)
ideal >>> filter

-}

-- | Linear extension to an /a/-compatible poset.
--
-- Think of 'Index' as a lawful 'Enum'.
--
-- See < https://en.wikipedia.org/wiki/Linear_extension >.
-- 
type Index a = (Yoneda a, Ring (Rep a))

incBy :: Index a => Rep a -> a -> a
incBy x = connl filter . (x<>) . connr filter

-- inc . dec = id?
-- dec . inc = id?
inc :: Index a => a -> a
inc = incBy sunit

decBy :: Index a => Rep a -> a -> a
decBy x = connl filter . (x<<) . connr filter

dec :: Index a => a -> a
dec = decBy sunit

-- | 
--
-- @'lower' x@ is the least element /y/ in the descending
-- chain such that @f y '>~' x@.
--
lower :: (Index a, Prd b) => a -> (a -> b) -> b -> a
lower z f x = while (\y -> f y >~ x) ge dec z
-- left

-- | 
--
-- @'lower'' x@ is the least element /y/ in the descending
-- chain such that @not $ f y '<~' x@.
--
lower' :: (Index a, Prd b) => a -> (a -> b) -> b -> a
lower' z f x = until (\y -> f y <~ x) ge dec z

--TODO check closure

-- | 
--
-- @'upper' y@ is the greatest element /x/ in the ascending
-- chain such that @g x '<~' y@.
--
upper :: (Index a, Prd b) => a -> (a -> b) -> b -> a
upper z g y = while (\x -> g x <~ y) le inc z


-- | 
--
-- @'upper'' y@ is the greatest element /x/ in the ascending
-- chain such that @not $ g z '>~' y@.
--
upper' :: (Index a, Prd b) => a -> (a -> b) -> b -> a
upper' z g y = until (\x -> g x >~ y) le inc z

-- | Covering relation on /a/.
--
-- < https://en.wikipedia.org/wiki/Covering_relation >
--
covers :: Eq a => Index a => a -> a -> Bool
covers x y = x `lt` y && all (not . lt x) (indexFrom x y)

-- | Constrained version of 'arr' from 'Control.Arrow'.
--
-- Essentially the same properties hold:
--
--  * @'arrow' id = 'Control.Category.id'@
--
--  * @'arrow' (f . g) = 'arrow' f >>> 'arrow' g@
--
--
--  * @'_1' ab >>> 'arrow' 'fst' = 'arrow' 'fst' >>> ab@
--
--  * @'_1' ('_1' ab) >>> 'arrow' 'assoc' = 'arrow' 'assoc' >>> '_1' ab@
--
--
--  * @ab >>> 'arrow' 'Left' = 'arrow' 'Left' >>> '_L' ab@
--
--  * @'_L' ('_L' ab) >>> 'arrow' 'assocsum' = 'arrow' 'assocsum' >>> '_L' ab@
--
-- where
--
-- > assoc ((a,b),c) = (a,(b,c))
-- > assocsum (Left (Left x)) = Left x
-- > assocsum (Left (Right y)) = Right (Left y)
-- > assocsum (Right z) = Right (Right z)
--
--
-- >>> conn = arrow (+1) :: Conn Int8 Int8
-- >>> _R conn 2
-- 1
-- >>> _R conn 1
-- 0
-- >>> _R conn 0
-- -1
--
arrow :: (Index a, Minimal a, Prd b) => (a -> b) -> Conn a b
arrow f = Conn f (upper' minimal f)

coarrow :: (Index a, Maximal a, Prd b) => (a -> b) -> Conn b a
coarrow g = Conn (lower' maximal g) g

inc' :: (Index a, Num (Idx a)) => a -> a
inc' = fromIndex . (+ 1) . toIndex

dec' :: (Index a, Num (Idx a)) => a -> a
dec' = fromIndex . subtract 1 . toIndex

step' :: (Num (Idx a), Index a) => Idx a -> a -> a
step' i = fromIndex . (+ i) . toIndex

fromIndex :: Index a => Idx a -> a
fromIndex = connr idx

toIndex :: Index a => a -> Idx a
toIndex = connl idx

--mapWithIdx :: (Idx a -> a -> a) -> a -> a -> a

foldWithIdx :: (Eq a, Index a) => (Idx a -> a -> a) -> a -> a -> a
foldWithIdx f x y = foldr' f x $ toIndex <$> indexFromTo x y 


{-

instance (Index a, Index b) => Index (a, b) where
    type Idx (a, b) = Product (Idx a) (Idx b)
    
    idx = idx *$* idx

step x = fmap 
dec = step (-1)
inc = step 1

instance (Index a, Index b) => Index (Either a b) where
    type Idx (Either a b) = Either (Idx a) (Idx b)
    
    idx = idx +++ idx
    inc = bimap inc inc
    dec = bimap dec dec
    step (Left x) = first (step x)
    step (Right x) = second (step x)

instance Index a => Index (Maybe a) where
    type Idx (Maybe a) = Maybe (Idx a)    

    idx = just idx
    inc = fmap inc
    dec = fmap dec
    step i = fmap (maybe id step i)

instance Index a => Index (Nan a) where
    type Idx (Nan a) = Nan (Idx a)    

    idx = def idx
    inc = mapNan inc
    dec = mapNan dec
    step i = mapNan (nan id step i) 
-}

-- >>> negate (inc @Float (-1/0)) == dec @Float (1/0)
-- True
--
-- >>> take 3 $ indexFrom' @Float 0
-- [0.0,1.0e-45,3.0e-45]
--
-- >>> take 3 $ indexFrom' @Float pInf
-- []
instance Index Float where 
    type Idx Float = Nan
    idx = f32u32 C.>>> u32w64
    inc = inc'
    dec = dec'

    step NaN = id
    step (Def i) = shift (fromIntegral i)

{-
instance Index Natural where 
    type Idx Natural = Natural
    idx = C.id
    inc = inc'
    dec = dec'
    step = step'

instance Index Word64 where 
    type Idx a = Word64
    idx = C.id
    inc = inc'
    dec = dec'
    step = step'

instance Index Word32 where 
    type Idx Word32 = Word32
    idx = C.id
    inc = inc'
    dec = dec'
    step = step'

instance Index Word16 where 
    type Idx Word16 = Word16
    idx = C.id
    inc = inc'
    dec = dec'
    step = step'

instance Index Word8 where 
    type Idx Word8 = Word8
    idx = C.id
    inc = inc'
    dec = dec'
    step = step'

instance Index Integer where 
    type Idx Integer = Integer
    idx = C.id
    inc = inc'
    dec = dec'
    step = step'

instance Index Int64 where 
    type Idx Int64 = Int64
    idx = C.id
    inc = inc'
    dec = dec'
    step = step'

instance Index Int32 where 
    type Idx Int32 = Int32
    idx = C.id
    inc = inc'
    dec = dec'
    step = step'

instance Index Int16 where 
    type Idx Int16 = Int16
    idx = C.id
    inc = inc'
    dec = dec'
    step = step'

instance Index Int8 where 
    type Idx Int8 = Int8
    idx = C.id
    inc = inc'
    dec = dec'
    step = step'
-}



contains :: Prd a => a -> a -> a -> Bool
contains x y z = x <~ z && z <~ y

{-
--indexRange :: Index a => Interval a -> Memo a -> Memo a -> Memo ([Idx a]) 
indexRange :: (Eq a, Index a, Idx a ~ Int) => a -> a -> Memo a
indexRange x y = Memo.switch (contains x y) (indexRange' x y ) id

indexRange' :: (Eq a, Index a, Idx a ~ Int) => a -> a -> Memo a 
indexRange' x y f z = (f <$> indexFromTo x y) !! (toIndex z)
-}

interval :: forall a. (Index a, Integral a) => Memo [Idx a]
interval = Memo.list $ memoizel (idx @a) Memo.integral

memoizel :: Conn a b -> Memo a -> Memo b
memoizel (Conn f g) = Memo.wrap f g

memoizer :: Conn a b -> Memo b -> Memo a
memoizer (Conn f g) = Memo.wrap g f

fib = Memo.integral fib'
  where
    fib' 0 = 0
    fib' 1 = 1
    fib' x = fib (x-1) + fib (x-2)




{-

indexFrom'' :: Index a => Interval a -> a
indexFrom'' (x, y) = while (<~ y) le inc x

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred f seed = 


indexFromToo (0, shift 10 0)

while :: Prd a => (a -> Bool) -> (a -> a) -> a -> a
while pred inc seed = go seed
  where go x | inc x =~ x = x
             | not (pred x') = x
             | otherwise = go x'
          where x' = f x

foo :: (Index t, Prd a) => t -> (t -> a) -> a -> [t]
foo z g y = whileM (\x -> g x <~ y) inc z

indexFromTo :: (Eq a, Index a) => a -> a -> [a]
indexFromTo x y = unfoldr f x where
  f x = let x' = inc x in if x' `gt` x && x <~ y
                             then Just (x, x') 
                             else Nothing

interval :: Index a => RangeMemo a
interval (x,y) = 

upper :: (Index a, Prd b) => a -> (a -> b) -> b -> a
upper z g y = while (\x -> g x <~ y) le inc z
-- @'upper'' y@ is the greatest element /x/ in the ascending
-- chain such that @not $ g z '>~' y@.
--
upper' :: (Index a, Prd b) => a -> (a -> b) -> b -> a
upper' z g y = until (\x -> g x >~ y) le inc z

-}



-- | The half-open interval /(x, y]/.
--
indexTo :: (Eq a, Index a) => a -> a -> [a]
indexTo x y = indexFrom (inc x) y

indexTo' :: (Eq a, Index a) => Interval a -> [a]
indexTo' = maybe [] (\(x,y) -> indexFrom (inc x) y) . endpts

enumerate :: Index a => a -> a -> [a]
enumerate x y = flip evalState x $
  whileM (get >>= \z -> return (z <~ y)) (modify inc >> get) 

-- | The half-open interval /[x, y)/.
--
indexFrom :: (Eq a, Index a) => a -> a -> [a]
indexFrom x y = unfoldr f x where
  f x = let x' = inc x in if x' `gt` x && x' <~ y
                             then Just (x, x') 
                             else Nothing

-- | The closed interval /[x, y]/.
--
-- Returns the list of values in the interval defined by a bounding pair.
--
-- Equivalent to 'enumFromTo'.
--
indexFromTo :: (Eq a, Index a) => a -> a -> [a]
indexFromTo x y = unfoldr f x where
  f x = let x' = inc x in if x' `gt` x && x <~ y
                             then Just (x, x') 
                             else Nothing


-- | Equivalent to 'enumFromThenTo'.
indexFromToBy :: (Eq a, Index a) => Idx a -> a -> a -> [a]
indexFromToBy i x y = unfoldr f x where
  f x = let x' = step i x in if x' `gt` x && x' <~ y
                             then Just (x, x') 
                             else Nothing

{-
type Dioid a = (Yoneda a, Semiring a)

properties:

inc is (strictly?) monotone, dec is (strictly?) antitone, 

inc . dec = dec . inc = id 

index :: Index a => Conn a (Down a)
index = Conn f g where
  f = Down . inc
  g x = dec x' where Down x' = x

class (Prd a, Prd (Idx a)) => Index a where 
    type Idx :: * -> *

    idx :: Conn a (Idx a)

    inc :: a -> a
    --inc = step unit

    dec :: a -> a
    --default dec :: Functor (Idx a)
    --dec = fromIndex . fmap (+1) . toIndex

    step :: Idx a -> a -> a
    --default step :: Idx a -> a -> a

https://en.wikipedia.org/wiki/Total_order#Chains
https://en.wikipedia.org/wiki/Completeness_(order_theory)
https://en.wikipedia.org/wiki/Chain-complete_partial_order
-}


