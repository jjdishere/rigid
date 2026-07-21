# Rigid analytic geometry formalization plan

## Initial scope

The first pass will treat a complete nontrivially normed field `K` with
`IsUltrametricDist K` and strict analytic geometry over `K`.

- Tate algebras initially have finitely many variables and unit polyradius.
- A strict affinoid algebra is presented as a continuous quotient of a Tate algebra.
- Berkovich points are contractive multiplicative real-valued seminorms extending the norm on `K`.
- Global spaces and morphisms will be built only after the affinoid theory and its sheaf theorem are
  available.
- `Rigid/Challenge.lean` is a standalone specification file. It has only mathlib imports and keeps
  the sorried target declarations independent of the eventual implementation import graph.

This deliberately postpones non-strict polyradii, trivially valued fields, adic spaces, and general
Huber pairs.

## Dependency order

### 1. Tate algebra

Reuse `MvPowerSeries.IsRestricted` from mathlib for the underlying restricted power series.

1. Define coordinates and the Gauss norm.
2. Construct the normed commutative `K`-algebra structure.
3. Prove the ultrametric inequality, multiplicativity of the Gauss norm, and completeness.
4. Prove density of polynomials and the universal property for power-bounded tuples.
5. Generalize to positive polyradii only after the strict unit-radius API is stable.

The multiplicativity proof is the first substantial algebraic milestone. It will likely need a
carefully chosen maximal coefficient argument rather than only generic norm estimates.

### 2. Affinoid algebra

1. Define quotient seminorms and prove completeness after quotienting by a closed ideal.
2. Bundle strict affinoid `K`-algebras and bounded/continuous homomorphisms.
3. Prove that algebra homomorphisms between affinoid algebras are continuous.
4. Prove Noetherianity (Tate's theorem).
5. Define rational and Weierstrass localizations and prove their universal properties.
6. Prove invariance under equivalent admissible Banach norms.

The current `IsAffinoidAlgebra` predicate records a continuous surjection. We must verify that this
is equivalent to the preferred quotient-norm formulation before treating it as final.

### 3. Affinoid geometry

1. Define rational domains and rational coverings.
2. Define the structure presheaf on the rational basis.
3. Prove Tate acyclicity for finite rational covers.
4. Extend the presheaf to the affinoid admissible site and prove the sheaf condition.
5. Define affinoid spectra and establish the contravariant algebra/geometry correspondence.

Tate acyclicity is the critical prerequisite for defining global rigid spaces as locally ringed
geometric objects.

### 4. Rigid spaces

1. Define admissible opens and admissible coverings (or a site presenting the same geometry).
2. Bundle locally affinoid locally ringed objects with analytic morphisms.
3. Construct gluing and open subspaces.
4. Define quasi-compact, quasi-separated, separated, and paracompact/finite-type-cover predicates.
5. Build the category and the affinoid spectrum functor.

### 5. Berkovich spaces

1. Put the evaluation topology on the Berkovich spectrum of an affinoid algebra.
2. Prove nonemptiness, compactness, and Hausdorffness.
3. Define completed residue fields and evaluation maps.
4. Define affinoid domains and analytic functions.
5. Build Berkovich spaces from affinoid atlases, then define good, strict, Hausdorff, and
   paracompact objects and analytic morphisms.

### 6. Comparison

1. Construct the comparison on affinoid objects and prove compatibility with rational domains.
2. Show that it respects admissible gluing and analytic morphisms.
3. Prove full faithfulness.
4. Characterize the essential image.
5. Package the result as `rigidToBerkovich_isEquivalence` and
   `rigidBerkovichEquivalence`.
6. Prove that separated rigid spaces correspond to Hausdorff Berkovich spaces.

## The comparison statement still needs a fixed reference

The predicates in `Rigid/Challenge.lean` currently encode the provisional comparison

- rigid side: locally affinoid, quasi-separated, and paracompact (typically via an affinoid cover of
  finite type);
- Berkovich side: good, strict, and paracompact.

Before proof work starts on the global comparison, choose a precise source and mirror its
conventions. In particular, verify:

- whether `good` is an assumption or follows from the chosen atlas convention;
- the exact rigid condition corresponding to Berkovich paracompactness;
- whether quasi-separatedness is independent or built into that condition;
- whether the base field must be nontrivially valued;
- whether Hausdorff/separated objects form the main equivalence or a restricted corollary.

Until these are settled, the comparison declarations are useful dependency targets rather than a
canonical theorem statement.

## Proposed file layout after the API stabilizes

```text
Rigid/
  TateAlgebra/Basic.lean
  TateAlgebra/GaussNorm.lean
  TateAlgebra/UniversalProperty.lean
  AffinoidAlgebra/Basic.lean
  AffinoidAlgebra/Localization.lean
  AffinoidAlgebra/Noetherian.lean
  AffinoidSpectrum/Basic.lean
  AffinoidSpectrum/TateAcyclicity.lean
  RigidSpace/Basic.lean
  RigidSpace/Gluing.lean
  Berkovich/Spectrum.lean
  Berkovich/Space.lean
  Comparison/Affinoid.lean
  Comparison/Global.lean
  Challenge.lean
```

Keep the implementation split by dependency. Once production modules exist, the root module should
import those modules rather than `Challenge.lean`; the challenge file remains a separately checked,
mathlib-only specification and may repeat production declaration names because the two import graphs
are not combined.

## Near-term milestone

Implement the strict Tate algebra through completeness and its universal property. This validates
that mathlib's restricted multivariate power series are the right foundation before introducing
quotients, sites, or global spaces.
