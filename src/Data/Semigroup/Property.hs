{-
quantales:

distributive_cross as bs = maybe True (~~ cross as bs) $ pjoin as <> pjoin bs
  where cross = join (liftA2 (<>) a b)

--lattice version
distributive_cross' as bs = cross as bs ~~ join as <> join bs
  where 
        cross = join (liftA2 (<>) a b)

join as \\ b ~~ meet (fmap (\\b) as)

a \\ meet bs ~~ meet (fmap (a\\) bs)

ideal_residuated :: (Quantale a, Ideal a, Functor (Rep a)) => a -> a -> Bool
ideal_residuated x y = x \\ y =~ join (fmap (x<>) (connl ideal $ y))

ideal_residuated' :: (Quantale a, Ideal a, Functor (Rep a)) => a -> a -> Bool
ideal_residuated' x y = x // y =~ join (fmap (<>x) (connl ideal $ y))

x \/ y = (x // y) <> y -- sunit (minus_plus x) y -- (y // x) + x
x /\ y = x <> (x \\ y) -- (y + x) // x -- x \\ (x + y) 

minimal \\ x =~ maximal =~ x \\ maximal
mempty \\ x ~~ sunit
 
-}



https://ncatlab.org/nlab/show/frame
http://ameql.math.muni.cz/sites/default/files/cintula.pdf

http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.608.4677&rep=rep1&type=pdf

examples (all on [0,1]):
1. Lukasiewicz t-norm: a <> b = max{0, a + b − 1}
2. Product t-norm: a <> b = a*b (the usual product of real numbers)
3. Minimum (or G¨odel) t-norm: a <> b = min{a, b}

a ⇒ L b =

1 if a ≤ b,
1 − a + b otherwise.
a ⇒Π b =

1 if a ≤ b,
b/a otherwise.
a ⇒G b =

1 if a ≤ b,
b otherwise.

A hoop can be defined as an algebra A = (A, ·, \\, mempty), where
(A, ·, mempty) is a commutative monoid and the following identities hold:


It is easy to see that the relation defined by a ≤ b iff mempty = a \\ b is a
partial order and that A is a hoop iff (A, ·, \\, 1, ≤) is an integral residuated
pomonoid that satisfies x <> (x \\ y) = y <> (y \\ x). 


A hoop A is Wajsberg if (a \\ b) \\ b = (b \\ a) \\ a for every a, b ∈ A. 
A is cancellative if a&b ≤ c&b implies a ≤ c, for every a, b, c ∈ A. 
A is bounded if it has a minimal element, and unbounded otherwise. 
A is said to be weakly cancellative if it is either cancellative or it
is bounded with a minimal element 0 and a&b ≤ c&b /= 0 implies a ≤ c, for every a, b, c ∈ A.

The order of a prelinear hoop defines a lattice structure where a ∧ b = a&(a \\ b)
and a ∨ b = ((a \\ b) \\ b) ∧ ((b \\ a) \\ a)

Show that, through duality, every t-norm ∗ generates a t-conorm ⊕ and
conversely according to:
a ⊕ b = 1 − [(1 − a) ∗ (1 − b)]
a ∗ b = 1 − [(1 − a) ⊕ (1 − b)].
In the literature on fuzzy sets, the triangular conorms ⊕ are considered as
generalizations of the set union and the triangular norms ∗ are considered as
generalizations of set intersection.

x \\ x = mempty,  
x<>(x \\ y) = y<>(y \\ x),  
(x<>y) \\ z = y \\ (x \\ z) (currying)
x <~ y <==> mempty ~~ x \\ y

admits a meet:
x /\ y = x <> (x \\ y) = cosunit (residl x) y


(x \\ y) \/ (y \\ x) ~~ ssunit (prelinear)

(a \\ b) \\ c <~ ((b \\ a) \\ c) \\ c (prelinear)
(x \\ y) \\ y ~~ (y \\ x) \\ x (Wajsberg)

If a hoop satisfies Wajsberg then it admits a join given by 

x \/ y = (x \\ y) \\ y.

otherwise?
x \/ y = ((x \\ y) \\ y) /\ ((y \\ x) \\ x)


 The following identities hold in every residuated lattice-ordered groupoid
(1) (x ∨ y)z = xz ∨ yz and z(x ∨ y) = zx ∨ zy.
(2) (x ∨ y)\z = x\z ∧ y\z and z\(x ∧ y) = z\x ∧ z\y.
(3) z/(x ∨ y) = z/x ∧ z/y and (x ∧ y)/z = x/z ∧ y/z.
(4) x(x\y) ≤ y and (y/x)x ≤ y.
(5) x ≤ y/(x\y) and x ≤ (y/x)\y.
(6) (y/(x\y))\y = x\y and y/((y/x)\y) = y/x.


The following identities and their mirror images hold in any residuated pomonoid.
--residuated lattices p 151
(1) (x\y)z ≤ x\yz,
(2) x\y ≤ zx\zy,
(3) (x\y)(y\z) ≤ x\z,
(4) xy\z ≤ y\(x\z),
(5) x\(y/z) = (x\y)/z,
(6) (x \\ mempty) <> y <~ x \\ y,
(7) mempty \\ x = x,
(8) mempty <~ x \\ x,
(9) x <> (x\\x) = x
(10) (x\x)<>(x\x) = x\x.
(11) x\y ≤ (z\x)\(z\y)
(12) x\y ≤ (x\z)/(y\z)


-- > x `ple` x <> y == Just (x \\ y)
-- > maybe y (x <>) (x \\ y) == y

-- > maybe x (<> y) (x \\ y) == x

-- > mon a b >>= (`lte` a) == Just True
-- > (a <> b) \\ b == Just a


(A, ≤) admits a meet operation defined by x∧y = x <> (x \\ y). Consequently,
every hoop satisfies the divisibility condition (Div). It turns out that not
all hoops have a lattice reduct; the ones that do are exactly the join-free
reducts of commutative, integral GBL-algebras. Also, among those, the
ones that satisfy prelinearity (PL) are exactly the reducts of BL-algebras
and are known as basic hoops; the corresponding subvariety of RL is denoted
by BH. 

further sub-varieties
BL-algebras as bounded commutative integral
residuated lattices satisfying the following two equations:
• Prelinearity: (x \\ y) ∨ (y \\ x) ≈ 1.
• Divisibility: x&(x \\ y) ≈ x ∧ y.

Thus, the algebraic structures defined by continuous t-norms are exactly the BL-algebras
over [0, 1]. There are some distinguished subclasses of BL-algebras:
Definition 2.5. Let A be a BL-algebra.
• A is an MV-algebra if it satisfies the involution equation: x ≈ (x \\ 0) \\ 0.
• A is a Π-algebra if it satisfies the cancellativity equation: (y \\ 0)∨((y \\ x&y) \\ x) ≈
1.
• A is a G-algebra if it satisfies the contraction equation: x ≈ x&x

Since they equationally given, these classes of algebras are in fact varieties. O



