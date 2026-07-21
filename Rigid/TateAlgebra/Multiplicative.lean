import Rigid.TateAlgebra.Leading
import Mathlib.RingTheory.MvPowerSeries.GaussNorm

set_option linter.style.header false

/-!
# Multiplicativity of the Tate algebra Gauss norm

The Gauss norm of a strict Tate series is attained at a coefficient. Given a monomial order, choose
the largest exponent attaining the norm in each of two nonzero series. In the coefficient of the
product at the sum of those exponents, the product of the two leading coefficients is the unique
summand of maximal norm. The nonarchimedean triangle inequality therefore prevents cancellation.
-/

open scoped MonomialOrder

universe u v

namespace Rigid.TateAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {ι : Type v}

private theorem norm_eq_mvp_gaussNorm (f : TateAlgebra K ι) :
    ‖f‖ = MvPowerSeries.gaussNorm (fun a : K ↦ ‖a‖) (fun _ : ι ↦ (1 : ℝ)) f.1 := by
  rw [norm_eq_sSup_coeff, MvPowerSeries.gaussNorm, sSup_range]
  congr 1
  funext n
  simp [Finsupp.prod]

/-- The Gauss norm is multiplicative whenever a monomial order on the variables is supplied. -/
theorem norm_mul_of_monomialOrder (m : MonomialOrder ι) (f g : TateAlgebra K ι) :
    ‖f * g‖ = ‖f‖ * ‖g‖ := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  let v : K → ℝ := fun a ↦ ‖a‖
  let c : ι → ℝ := fun _ ↦ 1
  have hfbd : MvPowerSeries.HasGaussNorm v c f.1 := by
    change BddAbove (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖ *
      n.prod (fun _ e ↦ (1 : ℝ) ^ e))
    simpa [Finsupp.prod] using bddAbove_range_norm_coeff K ι f
  have hgbd : MvPowerSeries.HasGaussNorm v c g.1 := by
    change BddAbove (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n g.1‖ *
      n.prod (fun _ e ↦ (1 : ℝ) ^ e))
    simpa [Finsupp.prod] using bddAbove_range_norm_coeff K ι g
  have hfgbd : MvPowerSeries.HasGaussNorm v c (f.1 * g.1) := by
    change BddAbove (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n (f.1 * g.1)‖ *
      n.prod (fun _ e ↦ (1 : ℝ) ^ e))
    simpa [Finsupp.prod] using bddAbove_range_norm_coeff K ι (f * g)
  have hdom : ∃ i j, MvPowerSeries.AchievesGaussNorm v c f.1 i ∧
      MvPowerSeries.AchievesGaussNorm v c g.1 j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (MvPowerSeries.coeff p.1 f.1 * MvPowerSeries.coeff p.2 g.1) <
          v (MvPowerSeries.coeff i f.1) * v (MvPowerSeries.coeff j g.1) := by
    refine ⟨leadingDegree m f, leadingDegree m g, ?_, ?_, ?_⟩
    · unfold MvPowerSeries.AchievesGaussNorm
      change ‖leadingCoeff m f‖ * (leadingDegree m f).prod (fun _ e ↦ (1 : ℝ) ^ e) =
        MvPowerSeries.gaussNorm v c f.1
      rw [norm_leadingCoeff m hf, norm_eq_mvp_gaussNorm]
      simp [Finsupp.prod, v, c]
    · unfold MvPowerSeries.AchievesGaussNorm
      change ‖leadingCoeff m g‖ * (leadingDegree m g).prod (fun _ e ↦ (1 : ℝ) ^ e) =
        MvPowerSeries.gaussNorm v c g.1
      rw [norm_leadingCoeff m hg, norm_eq_mvp_gaussNorm]
      simp [Finsupp.prod, v, c]
    · intro p hp hpair
      have hpadd : p.1 + p.2 = leadingDegree m f + leadingDegree m g :=
        Finset.mem_antidiagonal.mp hp
      have hsum := congrArg m.toSyn hpadd
      simp only [map_add] at hsum
      dsimp only [v]
      rw [_root_.norm_mul]
      rw [show ‖MvPowerSeries.coeff (leadingDegree m f) f.1‖ = ‖f‖ from
          norm_leadingCoeff m hf,
        show ‖MvPowerSeries.coeff (leadingDegree m g) g.1‖ = ‖g‖ from
          norm_leadingCoeff m hg]
      rcases lt_trichotomy (m.toSyn (leadingDegree m f)) (m.toSyn p.1) with hfi | heq | hif
      · have hflt : ‖MvPowerSeries.coeff p.1 f.1‖ < ‖f‖ :=
          norm_coeff_lt_of_leadingDegree_lt m hf hfi
        calc
          ‖MvPowerSeries.coeff p.1 f.1‖ * ‖MvPowerSeries.coeff p.2 g.1‖ ≤
              ‖MvPowerSeries.coeff p.1 f.1‖ * ‖g‖ :=
            mul_le_mul_of_nonneg_left (norm_coeff_le_norm K ι g p.2) (norm_nonneg _)
          _ < ‖f‖ * ‖g‖ := mul_lt_mul_of_pos_right hflt (norm_pos_iff.mpr hg)
      · exfalso
        apply hpair
        have hp1 : p.1 = leadingDegree m f := m.toSyn.injective heq.symm
        have hp2 : p.2 = leadingDegree m g := by
          apply add_left_cancel (a := leadingDegree m f)
          simpa only [hp1] using hpadd
        exact Prod.ext hp1 hp2
      · have hgj : m.toSyn (leadingDegree m g) < m.toSyn p.2 := by
          by_contra h
          have hp2le : m.toSyn p.2 ≤ m.toSyn (leadingDegree m g) := le_of_not_gt h
          have hlt := add_lt_add_of_lt_of_le hif hp2le
          rw [hsum] at hlt
          exact lt_irrefl _ hlt
        have hglt : ‖MvPowerSeries.coeff p.2 g.1‖ < ‖g‖ :=
          norm_coeff_lt_of_leadingDegree_lt m hg hgj
        calc
          ‖MvPowerSeries.coeff p.1 f.1‖ * ‖MvPowerSeries.coeff p.2 g.1‖ ≤
              ‖f‖ * ‖MvPowerSeries.coeff p.2 g.1‖ :=
            mul_le_mul_of_nonneg_right (norm_coeff_le_norm K ι f p.1) (norm_nonneg _)
          _ < ‖f‖ * ‖g‖ := mul_lt_mul_of_pos_left hglt (norm_pos_iff.mpr hf)
  have h := MvPowerSeries.gaussNorm_mul_eq_mul v c f.1 g.1 hfbd hgbd hfgbd
    (fun _ ↦ norm_nonneg _) norm_zero IsUltrametricDist.isNonarchimedean_norm _root_.norm_mul
    norm_neg (fun x hx ↦ norm_eq_zero.mp hx) (fun _ ↦ zero_lt_one) hdom
  rw [norm_eq_mvp_gaussNorm, norm_eq_mvp_gaussNorm, norm_eq_mvp_gaussNorm]
  exact h

/-- The Gauss norm on a Tate algebra in finitely many variables is multiplicative. -/
theorem norm_mul [Finite ι] (f g : TateAlgebra K ι) : ‖f * g‖ = ‖f‖ * ‖g‖ := by
  letI := Fintype.ofFinite ι
  letI := Classical.decEq ι
  letI := (Fintype.equivFin ι).linearOrder
  exact norm_mul_of_monomialOrder MonomialOrder.lex f g

end Rigid.TateAlgebra
