import Mathlib

set_option linter.style.header false

/-!
# Rigid analytic geometry challenge

This file is the target interface for a first formalization of rigid and Berkovich analytic
geometry. It imports only mathlib and is expected to compile while the declarations below still
contain `sorry`.

We first work over a complete, nontrivially normed, nonarchimedean field and with *strict* affinoid
algebras. The intended construction order is:

1. Tate algebras and their Gauss norms;
2. affinoid algebras, rational localizations, and affinoid spectra;
3. the admissible topology and Tate acyclicity;
4. rigid spaces obtained by gluing affinoid spectra;
5. Berkovich spectra and Berkovich spaces;
6. comparison functors and an equivalence on suitable full subcategories.

The predicates defining the comparison subcategories below are provisional. Before proving the
comparison theorem, they must be matched to a precise theorem in the literature; see `PLAN.md`.
-/

open CategoryTheory
open Filter
open scoped Topology

universe u v w

namespace Rigid

/-! ## Tate algebras -/

section TateAlgebra

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (ι : Type v)

/-- The underlying ring of the strict Tate algebra in variables indexed by `ι`.

Mathlib's restricted multivariate power series already give the correct underlying set: the
coefficients tend to zero along the cofinite filter. The missing work is the Gauss norm and its
analytic properties. The main development will initially assume that `ι` is finite. -/
abbrev TateAlgebra :=
  ↥(MvPowerSeries.IsRestricted.subring (R := K) (fun _ : ι ↦ (1 : ℝ)))

/-- The coordinate corresponding to a variable of the Tate algebra. -/
noncomputable def tateVariable (i : ι) : TateAlgebra K ι := sorry

/-- The Gauss norm, i.e. the supremum of the norms of the coefficients. -/
noncomputable def gaussNorm : TateAlgebra K ι → ℝ := sorry

noncomputable instance tateAlgebraNorm : Norm (TateAlgebra K ι) :=
  ⟨gaussNorm K ι⟩

noncomputable instance tateAlgebraNormedCommRing : NormedCommRing (TateAlgebra K ι) := sorry

noncomputable instance tateAlgebraAlgebra : Algebra K (TateAlgebra K ι) := sorry

noncomputable instance tateAlgebraNormedAlgebra : NormedAlgebra K (TateAlgebra K ι) := sorry

noncomputable instance tateAlgebraIsUltrametricDist : IsUltrametricDist (TateAlgebra K ι) := sorry

variable [Finite ι]

noncomputable instance tateAlgebraComplete [CompleteSpace K] : CompleteSpace (TateAlgebra K ι) :=
  sorry

/-- The Gauss norm is the supremum norm on coefficients. -/
theorem norm_eq_sSup_coeff (f : TateAlgebra K ι) :
    ‖f‖ = sSup (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖) := sorry

/-- The Gauss norm is multiplicative over a nonarchimedean field. -/
theorem norm_mul (f g : TateAlgebra K ι) : ‖f * g‖ = ‖f‖ * ‖g‖ := sorry

/-- The universal property of the strict Tate algebra.

A tuple in the closed unit polydisc of a complete nonarchimedean Banach `K`-algebra determines a
unique continuous `K`-algebra homomorphism. -/
theorem existsUnique_continuousAlgHom_of_norm_le_one [CompleteSpace K]
    {A : Type w} [SeminormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] (x : ι → A) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃! φ : ContinuousAlgHom K (TateAlgebra K ι) A,
      ∀ i, φ (tateVariable K ι i) = x i := sorry

end TateAlgebra

/-! ## Affinoid algebras and affinoid spectra -/

section AffinoidAlgebra

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- A strict `K`-affinoid algebra is a continuous quotient of a Tate algebra in finitely many
variables. -/
def IsAffinoidAlgebra : Prop :=
  ∃ (n : ℕ) (π : ContinuousAlgHom K (TateAlgebra K (Fin n)) A), Function.Surjective π

/-- Every algebra homomorphism between strict affinoid algebras is continuous. -/
theorem continuous_of_isAffinoidAlgebra
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (f : A →ₐ[K] B) : Continuous f := sorry

/-- Affinoid algebras are Noetherian. -/
theorem isNoetherianRing_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A) :
    IsNoetherianRing A := sorry

/-- A rational localization `A⟨T₁, ..., Tₙ⟩ / (gTᵢ - fᵢ)`.

The condition that `g, f₁, ..., fₙ` generate the unit ideal will be carried by rational-domain
constructors rather than by this raw algebra construction. -/
noncomputable def RationalLocalization
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] (n : ℕ) (g : A) (f : Fin n → A) : Type v := sorry

noncomputable instance rationalLocalizationNormedCommRing (n : ℕ) (g : A) (f : Fin n → A) :
    NormedCommRing (RationalLocalization K A n g f) := sorry

noncomputable instance rationalLocalizationAlgebra (n : ℕ) (g : A) (f : Fin n → A) :
    Algebra A (RationalLocalization K A n g f) := sorry

/-- A point of the Berkovich spectrum of `A`: a bounded multiplicative seminorm extending the norm
on `K`. The bound is normalized to be contractive. -/
structure BerkovichSpectrum where
  seminorm : MulRingSeminorm A
  map_algebraMap' : ∀ x : K, seminorm (algebraMap K A x) = ‖x‖
  le_norm' : ∀ a : A, seminorm a ≤ ‖a‖

instance berkovichSpectrumCoeFun : CoeFun (BerkovichSpectrum K A) (fun _ ↦ A → ℝ) :=
  ⟨fun x ↦ x.seminorm⟩

/-- The weakest topology for which evaluation at every element of `A` is continuous. -/
noncomputable instance berkovichSpectrumTopologicalSpace :
    TopologicalSpace (BerkovichSpectrum K A) := sorry

/-- Convergence in the Berkovich spectrum is pointwise convergence of seminorms. -/
theorem tendsto_iff_eval {l : Filter (BerkovichSpectrum K A)} {x : BerkovichSpectrum K A} :
    Tendsto id l (𝓝 x) ↔ ∀ a : A, Tendsto (fun y ↦ y a) l (𝓝 (x a)) := sorry

/-- The Berkovich spectrum of a nonzero affinoid algebra is nonempty. -/
theorem nonempty_berkovichSpectrum [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    Nonempty (BerkovichSpectrum K A) := sorry

/-- The Berkovich spectrum of an affinoid algebra is compact. -/
theorem isCompact_univ_berkovichSpectrum (hA : IsAffinoidAlgebra K A) :
    IsCompact (Set.univ : Set (BerkovichSpectrum K A)) := sorry

/-- The Berkovich spectrum is Hausdorff. -/
noncomputable instance berkovichSpectrumT2Space : T2Space (BerkovichSpectrum K A) := sorry

end AffinoidAlgebra

/-! ## Global rigid and Berkovich spaces

These declarations mark the intended global interfaces. Their implementations should eventually be
bundled locally ringed geometric objects, not opaque point sets. Their categories should use the
corresponding analytic morphisms.
-/

section GlobalSpaces

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- A rigid analytic space over `K`, locally modeled on strict affinoid spectra in an admissible
Grothendieck topology. -/
def RigidSpace
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] :
    Type (u + 1) := sorry

noncomputable instance rigidSpaceCategory : Category.{u + 1} (RigidSpace K) := sorry

namespace RigidSpace

/-- Every point has an admissible affinoid neighborhood. -/
def IsLocallyAffinoid (X : RigidSpace K) : Prop := sorry

/-- Intersections of quasi-compact admissible opens are quasi-compact. -/
def IsQuasiSeparated (X : RigidSpace K) : Prop := sorry

/-- The rigid-space finiteness condition used in the comparison theorem.

This is provisionally named `IsParacompact`; its final definition should be the standard condition
in the chosen rigid/Berkovich comparison theorem (typically formulated using an affinoid cover of
finite type). -/
def IsParacompact (X : RigidSpace K) : Prop := sorry

/-- The diagonal is a closed immersion. -/
def IsSeparated (X : RigidSpace K) : Prop := sorry

end RigidSpace

/-- A Berkovich analytic space over `K`, locally modeled on Berkovich spectra of affinoid
algebras. -/
def BerkovichSpace
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] :
    Type (u + 1) := sorry

noncomputable instance berkovichSpaceCategory : Category.{u + 1} (BerkovichSpace K) :=
  sorry

namespace BerkovichSpace

/-- Every point has an affinoid neighborhood. -/
def IsGood (X : BerkovichSpace K) : Prop := sorry

/-- The analytic atlas uses strict affinoid algebras. -/
def IsStrict (X : BerkovichSpace K) : Prop := sorry

/-- The underlying topological space is paracompact. -/
def IsParacompact (X : BerkovichSpace K) : Prop := sorry

/-- The underlying topological space is Hausdorff. -/
def IsHausdorff (X : BerkovichSpace K) : Prop := sorry

end BerkovichSpace

/-- Provisional rigid-side domain of the comparison equivalence. -/
def rigidComparisonProperty : ObjectProperty (RigidSpace K) :=
  fun X ↦ RigidSpace.IsLocallyAffinoid K X ∧ RigidSpace.IsQuasiSeparated K X ∧
    RigidSpace.IsParacompact K X

/-- Provisional Berkovich-side codomain of the comparison equivalence. -/
def berkovichComparisonProperty : ObjectProperty (BerkovichSpace K) :=
  fun X ↦ BerkovichSpace.IsGood K X ∧ BerkovichSpace.IsStrict K X ∧
    BerkovichSpace.IsParacompact K X

/-- The full subcategory of rigid spaces in the provisional comparison range. -/
abbrev ComparisonRigidSpace := (rigidComparisonProperty K).FullSubcategory

/-- The full subcategory of Berkovich spaces in the provisional comparison range. -/
abbrev ComparisonBerkovichSpace := (berkovichComparisonProperty K).FullSubcategory

/-- The comparison functor from rigid spaces to Berkovich spaces. -/
noncomputable def rigidToBerkovich : ComparisonRigidSpace K ⥤ ComparisonBerkovichSpace K := sorry

/-- Main comparison goal: the comparison functor is an equivalence of categories.

The exact full subcategories are provisional until a reference theorem has been selected and its
hypotheses have been encoded. -/
theorem rigidToBerkovich_isEquivalence :
    (rigidToBerkovich K).IsEquivalence := sorry

/-- Data-valued form of the main comparison theorem. -/
noncomputable def rigidBerkovichEquivalence :
    ComparisonRigidSpace K ≌ ComparisonBerkovichSpace K := sorry

/-- Under comparison, separated rigid spaces correspond to Hausdorff Berkovich spaces. -/
theorem separated_iff_hausdorff (X : ComparisonRigidSpace K) :
    RigidSpace.IsSeparated K X.obj ↔
      BerkovichSpace.IsHausdorff K ((rigidToBerkovich K).obj X).obj := sorry

end GlobalSpaces

end Rigid
