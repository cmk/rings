# Ordered Semirings

This library provides type classes for ordered (right) pre-semirings & semirings (sometimes called dioids), as well as some useful instances. The `Semiring` class imposes fairly minimal requirements—the various 'add-on' properties  (e.g. commutativity) are catalogued in `Data.Semiring.Property`.

Support for a wide range of pre-semirings and semirings and interoperability with `base` were primary considerations.

Why use semirings? They are simple extensions of the `Foldable` interface, so for all the same reasons you use folds: they reduce problem complexity and enable generic problem solving. The case for ordered semirings is more numerical in nature: they allow us to improve on a number of leaky abstractions associated with Haskell's numerical typeclasses and IEEE-754 (e.g. rounding, boundedness, associativity, distributivity, etc) using [a more precise notion of topology](https://en.wikipedia.org/wiki/Poset_topology).

## Basic Definitions

Unfortunately there is little standardization around the names of the structures defined by various relaxations of the ring axioms. In fact the ring axioms themselves are not without controversy: since [at least](https://en.wikipedia.org/wiki/Ring_(mathematics)#History) Noether's time, mathematicians have been in disagreement regarding whether to include muliplicative units in the definition of a ring, and by extension a semiring. Here we follow the terminology in Gondran & Minoux's _Graphs, Dioids and Semirings_.

A right pre-semiring (sometimes referred to as a bisemigroup) is a type `R` endowed with two associative binary operations: `<>` and `><`, along with a right-distributivity property connecting them:

```
(a <> b) >< c ≡ (a >< c) <> (b >< c)
```

A non-unital right semiring (sometimes referred to as a bimonoid) is a pre-semiring with a `mempty` element (aka `mempty`) that is right-neutral with respect to _both_  addition and multiplication (1):

```
mempty <> a ≡ a
mempty >< a ≡ a --1
```

Neutrality, distributivity, and the lack of a second unit lead to a distinct absorbtion property:

```
a >< b ≡ a >< b <> b
```

See also [Andrey's post](https://blogs.ncl.ac.uk/andreymokhov/united-monoids/#whatif) for more on (the commutative sub-class of) this class of structures.

Finally a unital right semiring is a pre-semiring with two distinct neutral elements, `mempty` and `unit`, such that `mempty` is right-neutral wrt addition, `unit` is right-neutral wrt multiplication, and `mempty` is now (2) right-annihilative wrt multiplication:

```
mempty <> a ≡ a
unit >< a ≡ a
mempty >< a ≡ mempty --2
```

See `Data.Semiring.Property` for a detailed specification of the laws.

Perhaps the easiest way to demonstrate the differences between the three families is through their respective universal folds:

```
-- No additive or multiplicative unit.
foldPresemiring :: Semiring r => (a -> r) -> NonEmpty (NonEmpty a) -> r
foldPresemiring = foldMap1 . product1

-- No multiplicative unit.
foldNonunital :: (Monoid r, Semiring r) => (a -> r) -> [NonEmpty a] -> r
foldNonunital = foldMap . product

-- Additive & multiplicative units.
foldUnital :: (Monoid r, Semiring r) => (a -> r) -> [[a]] -> r
foldUnital = foldMap . product -- ≡ const mempty if unit = mempty
```

The functions `product` and `product1` simply apply multiplication (with `unit` as the root in the case of `foldMap`) instead of addition, for example:

```
product :: (Foldable t, Monoid r, Semiring r) => (a -> r) -> t a -> r
product f = foldr' ((><) . f) unit
```

## Dioids

Given a commutative monoid (R,+,ε) unit can define a reflexive and transitive binary relation, referred to as the canonical preorder and denoted ≤:

a ≤ b ⇔ ∃ c ∈ R: b = a + c

The reflexivity (∀a ∈ R: a ≤ a) follows from the existence of a neutral element ε (a = a + ε) and the transitivity is immediate because a ≤ b ⇔ ∃ c ∈ R: b = a + c, and b ≤ d ⇔ ∃ c ∈ R: d = b + c. Hence d = a + c + c, which implies a ≤ d. 

Moreover since + is commutative, the canonical preorder relation of (R,+,ε) is compatible because a ≤ b ⇒ ∃ c ∈ R: b = a + c. Therefore we have that ∀d ∈ R:

b + d = a + c + d = a + d + c ⇒ a + d ≤ b + d

However since the antisymmetry of ≤ is not automatically satisfied, we can see that ≤ is only a preorder relation. We'll see in a moment that this is where the definition of a dioid will slot in. But first let's treat the non-commutative case.

When (R, +, ε) is a non-commutative monoid we can derive two canonical preorder relations as follows:

a ≤ b ⇔ ∃ c ∈ R: b = a + c 

a ≤' b ⇔ ∃ c ∈ R: b = c + a

Here again, the properties of reflexivity (ε being both left- and right-neutral) and transitivity are easily checked. Since we are primarily concerned with right-semirings, we will focus on ≤. Results will hold for both commutative semirings and non-commutative right-semirings.

A monoid (R, +, ε) is said to be canonically ordered when the canonical preorder relation ≤ of (R, +, ε) is an order relation, that is to say it also satisfies the property of antisymmetry: 

a ≤ b and b ≤ a ⇒ a = b.

It's a well-known theorem in semigroup theory that a non-trivial monoid cannot be both canonically _ordered_ (not just pre-ordered) and also have inverses (i.e. be a group). To see this it suffices to observe that if every element as an additive inverse then the order relation collapses to the trivial order and the resulting monoid consists only of ε.

Extending this result to semirings, we have that the family of semiring structures can be naturally subdivided into two disjoint sub-families depending on whether the addition operation satisfies unit of the following two properties:

- Addition endows the set R with a group structure;
- Addition endows the set R with a canonically ordered monoid structure.

In the first case, we are led to rings (imperfectly captured in `Num`), while in the second we are led to dioids: a (unital) dioid is a (unital) semiring R = (R, 0, 1, +, *) such that the preorder on R wrt + engenders a total order. Often this ordering arises because + is idempotent (e.g. `mean :: Fractional a => a -> a -> a`) or selective (e.g. `max :: Ord a => a -> a -> a`, `<|> :: Maybe a -> Maybe a -> Maybe a` etc).

So ordering is the defining property of dioids, and it gives rise to a sup topology (i.e. residuation) useful for solving 'linear' algebra problems in many applications in computer science, ranging from control theory to regular languages and Kleene algebras to shortest path algorithms using tropical dioids (e.g. max-plus). Dioids are also generalizations of distributive lattices and quantales, which have been studied extensively in mathematics and logic. The `codistributive` identity in `Data.Semiring.Property` provides the link between the two families.

Finally, it's worth noting that dioids encompass many of the various 'left-catch' laws in Haskell-land (e.g. `pure a <|> x ≡ pure`) as a result of the following positivity condition:

Given a dioid R, if a ∈ R, b ∈ R and a + b = ε, then a = ε and b = ε.

To see this, note that we have a + b = ε, which implies a ≤ ε and b ≤ ε. Since ε + a = a and ε + b = b we also have that ε ≤ a and ε ≤ b. From the antisymmetry of ≤ we then deduce a = ε and b = ε.

For example, given an `Alternative` with left-catch semantics (e.g. `Maybe`, `Either`, `IO` etc) we have the following correspondences:

Right annihilative `mempty`:

```
empty *> _ ≡ empty
mempty >< _ ≡ mempty
```

Right annihilative `unit`:

```
pure a <|> _ ≡ pure a
unit <> _ ≡ unit
```

If R is a dioid then this last property implies that:

```
(unit le) ≡ (unit ==)
```

Why? Because a right annihilativite multiplicative unit means that ∃ c ∈ R: 1 + c = a ⇔ 1 = a.

## Further Reading

- [A Survey of Residuated Lattices](https://www1.chapman.edu/~jipsen/reslat/rljt020206.pdf)
- Residuated Lattices: An Algebraic Glimpse at Substructural Logics
- [Fun with Semirings](http://stedolan.net/research/semirings.pdf)
- [From Monoids to Near-Semirings:
the Essence of MonadPlus and Alternative](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.723.1221&rep=rep1&type=pdf)
- [Semirings for Breakfast](https://marcpouly.ch/pdf/internal_100712.pdf)




