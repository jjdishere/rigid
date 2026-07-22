import Rigid.Berkovich.RelativeSpectrum
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.Quotient

set_option linter.style.header false

/-!
# Completed residue fields of Berkovich points

For a relative Berkovich point `x` on a normed `K`-algebra `A`, quotient `A` by the prime kernel of
`x`, extend the induced rank-one valuation to the fraction field, and complete. The resulting
`CompletedResidueField x` is a complete nontrivially normed nonarchimedean field over `K`. The
canonical evaluation map from `A` realizes the original seminorm exactly.
-/

open scoped NNReal

universe u v

namespace Rigid.BerkovichSpectrumOver

variable {K : Type u} [NontriviallyNormedField K]
variable {A : Type v} [NormedCommRing A] [Algebra K A] [IsUltrametricDist A]

/-- The `NNReal`-valued valuation associated to a relative Berkovich point. -/
noncomputable def valuation (x : Rigid.BerkovichSpectrumOver K A) : Valuation A ℝ≥0 where
  toFun a := ⟨x a, BerkovichSpectrumOver.nonneg K A x a⟩
  map_zero' := by ext; exact x.toBerkovichSpectrum.map_zero
  map_one' := by ext; exact x.toBerkovichSpectrum.map_one
  map_mul' a b := by ext; exact BerkovichSpectrumOver.map_mul K A x a b
  map_add_le_max' a b := by exact BerkovichSpectrumOver.map_add_le_max K A x a b

@[simp]
theorem valuation_apply (x : Rigid.BerkovichSpectrumOver K A) (a : A) :
    (valuation x a : ℝ) = x a := rfl

/-- The support of the associated valuation is the kernel of the Berkovich point. -/
theorem valuation_supp_eq_kernel (x : Rigid.BerkovichSpectrumOver K A) :
    (valuation x).supp = x.kernel := by
  ext a
  rw [Valuation.mem_supp_iff, BerkovichSpectrumOver.mem_kernel_iff]
  change (⟨x a, BerkovichSpectrumOver.nonneg K A x a⟩ : ℝ≥0) = 0 ↔ x a = 0
  simp

noncomputable instance kernelIsPrime (x : Rigid.BerkovichSpectrumOver K A) : x.kernel.IsPrime :=
  x.kernel_isPrime

/-- The integral residue domain obtained by quotienting by the point's prime kernel. -/
abbrev ResidueDomain (x : Rigid.BerkovichSpectrumOver K A) := A ⧸ x.kernel

/-- The fraction field of the integral residue domain. -/
abbrev ResidueFractionField (x : Rigid.BerkovichSpectrumOver K A) :=
  FractionRing (ResidueDomain x)

/-- The valuation induced on the integral residue domain. -/
noncomputable def quotientValuation (x : Rigid.BerkovichSpectrumOver K A) :
    Valuation (ResidueDomain x) ℝ≥0 :=
  (valuation x).onQuot (by rw [valuation_supp_eq_kernel])

@[simp]
theorem quotientValuation_supp (x : Rigid.BerkovichSpectrumOver K A) :
    (quotientValuation x).supp = 0 := by
  rw [quotientValuation, Valuation.supp_quot, valuation_supp_eq_kernel]
  exact Ideal.map_quotient_self x.kernel

/-- The valuation extended from the residue domain to its fraction field. -/
noncomputable def fractionValuation (x : Rigid.BerkovichSpectrumOver K A) :
    Valuation (ResidueFractionField x) ℝ≥0 :=
  (quotientValuation x).extendToLocalization (B := ResidueFractionField x) (by
    intro s hs
    rw [Ideal.mem_primeCompl_iff, quotientValuation_supp]
    exact nonZeroDivisors.ne_zero hs)

/-- The real-valued absolute value on the residue fraction field. -/
noncomputable def fractionAbsoluteValue (x : Rigid.BerkovichSpectrumOver K A) :
    AbsoluteValue (ResidueFractionField x) ℝ where
  toFun z := fractionValuation x z
  map_mul' a b := by simp
  nonneg' _ := NNReal.zero_le_coe
  eq_zero' a := by rw [NNReal.coe_eq_zero, (fractionValuation x).zero_iff]
  add_le' a b := by
    exact (NNReal.coe_le_coe.mpr ((fractionValuation x).map_add a b)).trans
      (max_le (le_add_of_nonneg_right NNReal.zero_le_coe)
        (le_add_of_nonneg_left NNReal.zero_le_coe))

noncomputable instance residueFractionNormedField (x : Rigid.BerkovichSpectrumOver K A) :
    NormedField (ResidueFractionField x) :=
  (fractionAbsoluteValue x).toNormedField

noncomputable instance residueFractionIsUltrametricDist
    (x : Rigid.BerkovichSpectrumOver K A) : IsUltrametricDist (ResidueFractionField x) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun a b => by
    change (fractionValuation x (a + b) : ℝ) ≤
      max (fractionValuation x a : ℝ) (fractionValuation x b : ℝ)
    exact_mod_cast (fractionValuation x).map_add a b

/-- The completed residue field of a relative Berkovich point. -/
abbrev CompletedResidueField (x : Rigid.BerkovichSpectrumOver K A) :=
  UniformSpace.Completion (ResidueFractionField x)

noncomputable instance completedResidueIsUltrametricDist
    (x : Rigid.BerkovichSpectrumOver K A) : IsUltrametricDist (CompletedResidueField x) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun a b => by
    induction a, b using UniformSpace.Completion.induction_on₂ with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a b =>
        simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe] using
          IsUltrametricDist.norm_add_le_max a b

/-- The canonical map from the original algebra to the residue fraction field. -/
noncomputable def residueFractionMap (x : Rigid.BerkovichSpectrumOver K A) :
    A →+* ResidueFractionField x :=
  (algebraMap (ResidueDomain x) (ResidueFractionField x)).comp (Ideal.Quotient.mk x.kernel)

@[simp]
theorem norm_residueFractionMap (x : Rigid.BerkovichSpectrumOver K A) (a : A) :
    ‖residueFractionMap x a‖ = x a := by
  change (fractionValuation x (algebraMap (ResidueDomain x) (ResidueFractionField x)
    (Ideal.Quotient.mk x.kernel a)) : ℝ≥0) = x a
  rw [fractionValuation, Valuation.extendToLocalization_apply_map_apply]
  rfl

/-- The canonical evaluation map from the original algebra to the completed residue field. -/
noncomputable def completedResidueMap (x : Rigid.BerkovichSpectrumOver K A) :
    A →+* CompletedResidueField x :=
  UniformSpace.Completion.coeRingHom.comp (residueFractionMap x)

/-- The completed residue evaluation realizes the Berkovich seminorm exactly. -/
@[simp]
theorem norm_completedResidueMap (x : Rigid.BerkovichSpectrumOver K A) (a : A) :
    ‖completedResidueMap x a‖ = x a := by
  change ‖(residueFractionMap x a : CompletedResidueField x)‖ = x a
  rw [UniformSpace.Completion.norm_coe, norm_residueFractionMap]

noncomputable instance completedResidueAlgebra (x : Rigid.BerkovichSpectrumOver K A) :
    Algebra K (CompletedResidueField x) :=
  ((completedResidueMap x).comp (algebraMap K A)).toAlgebra

@[simp]
theorem norm_algebraMap_completedResidueField
    (x : Rigid.BerkovichSpectrumOver K A) (r : K) :
    ‖algebraMap K (CompletedResidueField x) r‖ = ‖r‖ := by
  change ‖completedResidueMap x (algebraMap K A r)‖ = ‖r‖
  rw [norm_completedResidueMap, x.map_algebraMap]

noncomputable instance completedResidueNormedAlgebra (x : Rigid.BerkovichSpectrumOver K A) :
    NormedAlgebra K (CompletedResidueField x) where
  norm_smul_le r y := by
    rw [Algebra.smul_def, norm_mul, norm_algebraMap_completedResidueField]

noncomputable instance completedResidueNontriviallyNormedField
    (x : Rigid.BerkovichSpectrumOver K A) : NontriviallyNormedField (CompletedResidueField x) :=
  ⟨let ⟨r, hr⟩ := NontriviallyNormedField.non_trivial (α := K)
   ⟨algebraMap K (CompletedResidueField x) r, by
    rwa [norm_algebraMap_completedResidueField]⟩⟩

/-- The completed residue evaluation as a `K`-algebra homomorphism. -/
noncomputable def completedResidueAlgHom (x : Rigid.BerkovichSpectrumOver K A) :
    A →ₐ[K] CompletedResidueField x where
  __ := completedResidueMap x
  commutes' _ := rfl

@[simp]
theorem completedResidueAlgHom_apply
    (x : Rigid.BerkovichSpectrumOver K A) (a : A) :
    completedResidueAlgHom x a = completedResidueMap x a := rfl

@[simp]
theorem norm_completedResidueAlgHom
    (x : Rigid.BerkovichSpectrumOver K A) (a : A) :
    ‖completedResidueAlgHom x a‖ = x a :=
  norm_completedResidueMap x a

/-- The kernel of completed residue evaluation is the point's prime kernel. -/
@[simp]
theorem ker_completedResidueMap (x : Rigid.BerkovichSpectrumOver K A) :
    RingHom.ker (completedResidueMap x) = x.kernel := by
  ext a
  rw [RingHom.mem_ker, ← norm_eq_zero, norm_completedResidueMap,
    BerkovichSpectrumOver.mem_kernel_iff]

end Rigid.BerkovichSpectrumOver
