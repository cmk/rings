{-# Language ConstraintKinds #-}
{-# Language Rank2Types #-}

module Data.Dioid.Signed where

import Data.Bifunctor (first)
import Data.Connection hiding (first)
import Data.Connection.Float
import Data.Float
import Data.Float.Instance
import Data.Ord (Down(..))
import Data.Prd
import Data.Prd.Lattice
import Data.Quantale
import Data.Semiring
import Prelude

-- | 'Sign' is isomorphic to 'Maybe Ordering' and (Bool,Bool), but has a distinct poset ordering:
--
-- @ 'Indeterminate' >= 'Positive' >= 'Zero'@ and
-- @ 'Indeterminate' >= 'Negative' >= 'Zero'@ 
--
-- Note that 'Positive' and 'Negative' are not comparable. 
--
--   * 'Positive' can be regarded as representing (0, +∞], 
--   * 'Negative' as representing [−∞, 0), 
--   * 'Indeterminate' as representing [−∞, +∞] v NaN, and 
--   * 'Zero' as representing the set {0}.
--
data Sign = Zero | Negative | Positive | Indeterminate deriving (Show, Eq)

signOf :: (Eq a, Num a, Prd a) => a -> Sign
signOf x = case sign x of
    Nothing -> Indeterminate
    Just EQ -> Zero
    Just LT -> Negative
    Just GT -> Positive

instance Semigroup Sign where
    Positive <> Positive            = Positive
    Positive <> Negative            = Indeterminate
    Positive <> Zero                = Positive
    Positive <> Indeterminate       = Indeterminate

    Negative <> Positive            = Indeterminate
    Negative <> Negative            = Negative
    Negative <> Zero                = Negative
    Negative <> Indeterminate       = Indeterminate

    Zero <> a                       = a

    Indeterminate <> _              = Indeterminate

instance Monoid Sign where
    mempty = Zero

instance Semiring Sign where
    Positive >< a = a

    Negative >< Positive            = Negative
    Negative >< Negative            = Positive
    Negative >< Zero                = Zero
    Negative >< Indeterminate       = Indeterminate

    Zero >< _                       = Zero

    --NB: measure theoretic zero
    Indeterminate >< Zero           = Zero
    Indeterminate >< _              = Indeterminate

    fromBoolean = fromBooleanDef Positive

-- TODO if we dont use canonical ordering then we can define a
-- monotone map to floats
instance Prd Sign where
    Positive <~ Positive         = True
    Positive <~ Negative         = False
    Positive <~ Zero             = False
    Positive <~ Indeterminate    = True 

    Negative <~ Positive         = False
    Negative <~ Negative         = True
    Negative <~ Zero             = False
    Negative <~ Indeterminate    = True
    
    --Zero <~ Indeterminate        = False
    Zero <~ _                    = True

    Indeterminate <~ Indeterminate  = True
    Indeterminate <~ _              = False

instance Min Sign where
    minimal = Zero

instance Max Sign where
    maximal = Indeterminate

instance Bounded Sign where
    minBound = minimal
    maxBound = maximal

-- Signed

newtype Signed = Signed { unSigned :: Float }

instance Show Signed where
    show (Signed x) = show x

instance Eq Signed where
    (Signed x) == (Signed y) | isNan x && isNan y = True 
                             | isNan x || isNan y = False
                             | otherwise = split x == split y -- 0 /= -0

instance Prd Signed where
    Signed x <~ Signed y | isNan x && isNan y = True
                         | isNan x || isNan y = False
                         | otherwise = (first Down $ split x) <~ (first Down $ split y)

    pcompare (Signed x) (Signed y) | isNan x && isNan y = Just EQ 
                                   | isNan x || isNan y = Nothing 
                                   | otherwise = pcompare (first Down $ split x) (first Down $ split y)

f32sgn :: Conn Float Signed
f32sgn = Conn f g where
  f x | x == nInf = Signed $ -0
      | otherwise = Signed $ either (const 0) id $ split x

  g (Signed x) = either (const nInf) id $ split x

ugnsgn :: Conn Unsigned Signed
ugnsgn = Conn f g where
  f (Unsigned x) = Signed $ abs x
  g (Signed x) = Unsigned $ either (const 0) id $ split x

{-
ugnf32 :: Conn Unsigned (Down Float)
ugnf32 = Conn f g where
  g (Down x) = Unsigned . max 0 $ x
  f (Unsigned x) = Down x
-}

--TODO 
--dont export constructor, qquoters and/or rebindable syntax

newtype Unsigned = Unsigned Float

unsigned :: Signed -> Unsigned
unsigned (Signed x) = Unsigned (abs x)

instance Show Unsigned where
    show (Unsigned x) = show $ abs x

instance Eq Unsigned where
    (Unsigned x) == (Unsigned y) | finite x && finite y = (abs x) == (abs y) 
                                 | not (finite x) && not (finite y) = True
                                 | otherwise = False

-- Unsigned has a 2-Ulp interval semiorder containing all joins and meets.
instance Prd Unsigned where
    u <~ v = u `ltugn` v || u == v 

ltugn :: Unsigned -> Unsigned -> Bool
ltugn (Unsigned x) (Unsigned y) | finite x && finite y = (abs x) < shift (-2) (abs y) 
                                | finite x && not (finite y) = True
                                | otherwise = False

instance Min Unsigned where
    minimal = Unsigned 0

instance Max Unsigned where
    maximal = Unsigned pInf

instance Lattice Unsigned where
  (Unsigned x) \/ (Unsigned y) | finite x && finite y = Unsigned $ max (abs x) (abs y)
                               | otherwise = Unsigned x

  (Unsigned x) /\ (Unsigned y) | finite x && finite y = Unsigned $ min (abs x) (abs y)
                               | not (finite x)  && finite y = Unsigned y
                               | otherwise = Unsigned x

instance Semigroup Unsigned where
    Unsigned x <> Unsigned y = Unsigned $ abs x + abs y

instance Monoid Unsigned where
    mempty = Unsigned 0

instance Semiring Unsigned where
    Unsigned x >< Unsigned y | zero x || zero y = Unsigned 0
                             | otherwise = Unsigned $ abs x * abs y

    fromBoolean = fromBooleanDef (Unsigned 1)

instance Quantale Unsigned where
    x \\ y = y // x

    Unsigned y // Unsigned x = Unsigned . max 0 $ y // x
