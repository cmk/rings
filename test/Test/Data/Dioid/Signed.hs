{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Dioid.Signed where

import Prelude 

import Data.Ord (Down(..))
import Data.Prd
import Data.Semiring
import Data.Connection
import Data.Dioid.Signed
import Data.Float
import Data.Semigroup.Quantale

import qualified Data.Prd.Property as Prop
import qualified Data.Semiring.Property as Prop
import qualified Data.Connection.Property as Prop

import Hedgehog
import Test.Data.Float
import Test.Property.Util
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

gen_sign :: Gen Sign
gen_sign = G.choice $ fmap pure [Zero, Positive, Negative, Indeterminate]

gen_signed :: Gen Signed
gen_signed = Signed <$> gen_flt32'

gen_unsigned :: Gen Unsigned
gen_unsigned = Unsigned <$> gen_flt32

gen_unsigned' :: Gen Unsigned
gen_unsigned' = Unsigned <$> gen_flt32'

prop_prd_signed :: Property
prop_prd_signed = withTests 1 $ property $ do
  x <- forAll gen_signed
  y <- forAll gen_signed
  z <- forAll gen_signed

  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z

prop_connection_flt32_signed :: Property
prop_connection_flt32_signed = withTests 1 $ property $ do
  x <- forAll gen_flt32'
  y <- forAll gen_signed
  x' <- forAll gen_flt32'
  y' <- forAll gen_signed

  assert $ Prop.connection f32sgn x y
  assert $ Prop.monotone' f32sgn x x'
  assert $ Prop.monotone  f32sgn y y'
  assert $ Prop.closed f32sgn x
  assert $ Prop.kernel f32sgn y 

prop_prd_unsigned :: Property
prop_prd_unsigned = withTests 1000 $ property $ do
  x <- forAll gen_unsigned'
  y <- forAll gen_unsigned'
  z <- forAll gen_unsigned'
  w <- forAll gen_unsigned'

  assert $ Prop.reflexive_eq x
  assert $ Prop.reflexive_le x
  assert $ Prop.irreflexive_lt x
  assert $ Prop.symmetric x y
  assert $ Prop.asymmetric x y
  assert $ Prop.antisymmetric x y
  assert $ Prop.transitive_lt x y z
  assert $ Prop.transitive_le x y z
  assert $ Prop.transitive_eq x y z

  assert $ Prop.connex x y
  assert $ Prop.semiconnex x y
  assert $ Prop.trichotomous x y
  assert $ Prop.chain_22 x y z w
  assert $ Prop.chain_31 x y z w

prop_semiring_unsigned :: Property
prop_semiring_unsigned = withTests 1000 $ property $ do
  x <- forAll gen_unsigned'
  y <- forAll gen_unsigned'
  z <- forAll gen_unsigned'

  assert $ Prop.annihilative_multiplication x
  assert $ Prop.neutral_addition' x
  assert $ Prop.neutral_multiplication' x
  assert $ Prop.associative_addition x y z
  assert $ Prop.associative_multiplication x y z
  assert $ Prop.distributive x y z

prop_quantale_unsigned :: Property
prop_quantale_unsigned = withTests 1000 . withShrinks 0 $ property $ do
  x <- forAll gen_unsigned -- we do not require `residr pInf` etc
  y <- forAll gen_unsigned'
  z <- forAll gen_unsigned'

  --assert $ Prop.connection (residl x) y z
  assert $ Prop.connection (residr x) y z

  --assert $ Prop.monotone' (residl x) y z
  assert $ Prop.monotone' (residr x) y z

  --assert $ Prop.monotone (residl x) y z
  assert $ Prop.monotone (residr x) y z

  --assert $ Prop.closed (residl x) y
  assert $ Prop.closed (residr x) y

  --assert $ Prop.kernel (residl x) y
  assert $ Prop.kernel (residr x) y

  assert $ residuated x y z


f32ugn :: Conn Float Unsigned
f32ugn = Conn f g where
  f x | finite x  = Unsigned $ max 0 $ x
      | otherwise = Unsigned x
  g (Unsigned x) = x

mono f x y = x <~ y ==> f x <~ f y

{-
u = Unsigned
f = id :: Float -> Float

x = u 2.3380933
y = u 6.049403

x = u 0.37794903
y = u 0.3269925

x = f 2.3380933
y = f 6.049403

x = f 0.37794903
y = f 0.3269925

counit (residl x) y


residl x = Conn (<>x) . (//x) $ y

(//x) . (<>x) $ y

x = u 1
shift' n (Unsigned x) = Unsigned $ shift n x
xs = flip shift' x <$> [-4,-3,-2,-1,0,1,2,3,4]
fmap (cvn x) xs
y = shift' 2 x
z = shift' 4 x
Prop.transitive_eq x y z


fmap (cvn x) xs
λ> fmap (Prop.semiconnex x) xs
[True,True,False,False,True,False,False,True,True]
λ> fmap (<~ x) xs
[True,True,False,False,True,False,False,False,False]
λ> fmap (~~ x) xs
[False,False,True,True,True,True,True,False,False]
-}

{-
prop_connection_flt32_unsigned :: Property
prop_connection_flt32_unsigned = withTests 1000 $ property $ do
  x <- forAll gen_flt32
  y <- forAll gen_unsigned
  x' <- forAll gen_flt32
  y' <- forAll gen_unsigned

  assert $ Prop.connection f32ugn x y
  assert $ Prop.monotone' f32ugn x x'
  assert $ mono (connr f32ugn) y y'
  assert $ Prop.closed f32ugn x
  assert $ Prop.kernel f32ugn y 
-}

{-
prop_connection_unsigned_signed :: Property
prop_connection_unsigned_signed = withTests 10000 $ property $ do
  x <- forAll gen_unsigned
  y <- forAll gen_signed
  x' <- forAll gen_unsigned
  y' <- forAll gen_signed

  assert $ Prop.connection ugnsgn x y
  assert $ Prop.monotone' ugnsgn x x'
  assert $ Prop.monotone  ugnsgn y y'
  assert $ Prop.closed ugnsgn x
  assert $ Prop.kernel ugnsgn y 
-}


tests :: IO Bool
tests = checkParallel $$(discover)
