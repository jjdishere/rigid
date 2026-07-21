import Rigid.Berkovich.GeneralSmoothing
import Rigid.Berkovich.Spectrum
import Mathlib.Analysis.Normed.Unbundled.SeminormFromBounded
import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst

set_option linter.style.header false

open scoped Topology BigOperators

universe u

namespace Rigid.BerkovichSpectrum

/-!
# Nonemptiness of the Berkovich spectrum

This file proves that the Berkovich spectrum of every nonzero commutative normed ring is nonempty.
First the given norm is normalized and spectrally smoothed to a power-multiplicative ring seminorm.
For each ring element, `seminormFromConst` makes that element multiplicative while preserving
multiplicativity at elements already treated. Compactness and the finite intersection property then
produce a seminorm that is multiplicative at every element.
-/

section

variable (R : Type u) [NormedCommRing R]

private abbrev SeminormBox := ∀ a : R, Set.Icc (0 : ℝ) ‖a‖

private def IsCandidate (f : SeminormBox R) : Prop :=
  (f 0 : ℝ) = 0 ∧
  (f 1 : ℝ) = 1 ∧
  (∀ a b, (f (a + b) : ℝ) ≤ f a + f b) ∧
  (∀ a, (f (-a) : ℝ) = f a) ∧
  (∀ a b, (f (a * b) : ℝ) ≤ f a * f b) ∧
  IsPowMul (fun a ↦ (f a : ℝ))

private abbrev Candidate := {f : SeminormBox R // IsCandidate R f}

private theorem continuous_eval_candidate (a : R) :
    Continuous fun p : Candidate R ↦ (p.1 a : ℝ) := by
  have hsub : Continuous fun p : Candidate R ↦ p.1 := continuous_subtype_val
  have heval : Continuous fun f : SeminormBox R ↦ f a := continuous_apply a
  exact continuous_subtype_val.comp (heval.comp hsub)

private theorem isClosed_isCandidate : IsClosed {f : SeminormBox R | IsCandidate R f} := by
  let Z : Set (SeminormBox R) := {f | (f 0 : ℝ) = 0}
  let O : Set (SeminormBox R) := {f | (f 1 : ℝ) = 1}
  let A : Set (SeminormBox R) := ⋂ a, ⋂ b, {f | (f (a + b) : ℝ) ≤ f a + f b}
  let N : Set (SeminormBox R) := ⋂ a, {f | (f (-a) : ℝ) = f a}
  let M : Set (SeminormBox R) := ⋂ a, ⋂ b, {f | (f (a * b) : ℝ) ≤ f a * f b}
  let P : Set (SeminormBox R) := ⋂ a, ⋂ n, ⋂ (_h : 1 ≤ n),
    {f | (f (a ^ n) : ℝ) = (f a : ℝ) ^ n}
  have hset : {f : SeminormBox R | IsCandidate R f} =
      Z ∩ (O ∩ (A ∩ (N ∩ (M ∩ P)))) := by
    ext f
    simp only [IsCandidate, Z, O, A, N, M, P, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter, IsPowMul]
  rw [hset]
  have hZ : IsClosed Z := isClosed_eq (by fun_prop) continuous_const
  have hO : IsClosed O := isClosed_eq (by fun_prop) continuous_const
  have hA : IsClosed A := by
    dsimp only [A]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_le (by fun_prop) (by fun_prop)
  have hN : IsClosed N := by
    dsimp only [N]
    exact isClosed_iInter fun a ↦ isClosed_eq (by fun_prop) (by fun_prop)
  have hM : IsClosed M := by
    dsimp only [M]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_le (by fun_prop) (by fun_prop)
  have hP : IsClosed P := by
    dsimp only [P]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
      isClosed_eq (by fun_prop) (by fun_prop)
  exact hZ.inter (hO.inter (hA.inter (hN.inter (hM.inter hP))))

private noncomputable instance candidateCompactSpace : CompactSpace (Candidate R) :=
  isCompact_iff_compactSpace.mp (isClosed_isCandidate R).isCompact

private def Candidate.toRingSeminorm {R : Type u} [NormedCommRing R]
    (p : Candidate R) : RingSeminorm R where
  toFun a := p.1 a
  map_zero' := p.2.1
  add_le' := p.2.2.2.1
  neg' := p.2.2.2.2.1
  mul_le' := p.2.2.2.2.2.1

private theorem Candidate.map_one {R : Type u} [NormedCommRing R]
    (p : Candidate R) : p.toRingSeminorm 1 = 1 := p.2.2.1
private theorem Candidate.powMul {R : Type u} [NormedCommRing R]
    (p : Candidate R) : IsPowMul p.toRingSeminorm :=
  p.2.2.2.2.2.2

private def Candidate.ofRingSeminorm (f : RingSeminorm R) (hone : f 1 = 1)
    (hpow : IsPowMul f) (hle : ∀ a, f a ≤ ‖a‖) : Candidate R :=
  ⟨fun a ↦ ⟨f a, apply_nonneg f a, hle a⟩,
    _root_.map_zero f, hone, fun a b ↦ map_add_le_add f a b, fun a ↦ map_neg_eq_map f a,
    fun a b ↦ map_mul_le_mul f a b, hpow⟩

private noncomputable def initialCandidate [Nontrivial R] : Candidate R := by
  have hmul : ∀ a b : R, ‖a * b‖ ≤ (1 : ℝ) * ‖a‖ * ‖b‖ := by
    intro a b
    simpa using norm_mul_le a b
  let g : RingSeminorm R := seminormFromBounded
    (f := fun a : R ↦ ‖a‖) (c := 1) norm_zero norm_nonneg hmul norm_add_le norm_neg
  have hnorm_ne : (fun a : R ↦ ‖a‖) ≠ 0 := by
    intro h
    have h1 := congr_fun h (1 : R)
    simpa using (norm_pos_iff.mpr (one_ne_zero : (1 : R) ≠ 0)).ne' h1
  have hg_one : g 1 = 1 := seminormFromBounded_one hnorm_ne norm_nonneg hmul
  have hg_one_le : g 1 ≤ 1 := hg_one.le
  let f : RingSeminorm R := Rigid.spectralSmoothingSeminorm g hg_one_le
  have hf_one : f 1 = 1 := by
    change smoothingFun g 1 = 1
    rw [smoothingFun_of_powMul g hg_one_le (x := 1)]
    · exact hg_one
    · intro n hn
      simp [hg_one]
  refine Candidate.ofRingSeminorm R f hf_one
    (Rigid.isPowMul_spectralSmoothingSeminorm g hg_one_le) ?_
  intro a
  exact (Rigid.spectralSmoothingSeminorm_le g hg_one_le a).trans <| by
    change seminormFromBounded' (fun x : R ↦ ‖x‖) a ≤ ‖a‖
    simpa using seminormFromBounded_le norm_nonneg hmul a

private def mulAt (c : R) : Set (Candidate R) :=
  {p | ∀ a, p.toRingSeminorm (c * a) = p.toRingSeminorm c * p.toRingSeminorm a}

private theorem isClosed_mulAt (c : R) : IsClosed (mulAt R c) := by
  change IsClosed {p : Candidate R | ∀ a,
    (p.1 (c * a) : ℝ) = (p.1 c : ℝ) * (p.1 a : ℝ)}
  rw [show {p : Candidate R | ∀ a,
      (p.1 (c * a) : ℝ) = (p.1 c : ℝ) * (p.1 a : ℝ)} =
      ⋂ a, {p | (p.1 (c * a) : ℝ) = (p.1 c : ℝ) * (p.1 a : ℝ)} by
    ext p
    simp]
  exact isClosed_iInter fun a ↦ isClosed_eq (continuous_eval_candidate R (c * a))
    ((continuous_eval_candidate R c).mul (continuous_eval_candidate R a))

private noncomputable def improve (p : Candidate R) (c : R) : Candidate R := by
  by_cases hc : p.toRingSeminorm c = 0
  · exact p
  · let q : RingSeminorm R := seminormFromConst p.map_one.le hc p.powMul
    refine Candidate.ofRingSeminorm R q (seminormFromConst_one p.map_one.le hc p.powMul)
      (seminormFromConst_isPowMul p.map_one.le hc p.powMul) ?_
    intro a
    exact (seminormFromConst_le_seminorm p.map_one.le hc p.powMul a).trans (p.1 a).2.2

private theorem improve_mem_mulAt (p : Candidate R) (c : R) : improve R p c ∈ mulAt R c := by
  change ∀ a, (improve R p c).toRingSeminorm (c * a) =
    (improve R p c).toRingSeminorm c * (improve R p c).toRingSeminorm a
  intro a
  unfold improve
  split_ifs with hc
  · apply le_antisymm
    · exact (map_mul_le_mul p.toRingSeminorm c a).trans_eq (by rw [hc, zero_mul])
    · rw [hc, zero_mul]
      exact apply_nonneg p.toRingSeminorm (c * a)
  · exact seminormFromConst_const_mul p.map_one.le hc p.powMul a

private theorem improve_mem_mulAt_of_mem (p : Candidate R) {c d : R} (hd : p ∈ mulAt R d) :
    improve R p c ∈ mulAt R d := by
  change ∀ a, (improve R p c).toRingSeminorm (d * a) =
    (improve R p c).toRingSeminorm d * (improve R p c).toRingSeminorm a
  intro a
  unfold improve
  split_ifs with hc
  · exact hd a
  · exact seminormFromConst_isMul_of_isMul p.map_one.le hc p.powMul hd a

private theorem exists_mem_mulAt_finset [Nontrivial R] (s : Finset R) :
    ∃ p : Candidate R, ∀ c ∈ s, p ∈ mulAt R c := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨initialCandidate R, by simp⟩
  | @insert c s hc ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨improve R p c, ?_⟩
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact improve_mem_mulAt R p d
    · exact improve_mem_mulAt_of_mem R p (hp d hd)

/-- The Berkovich spectrum of a nonzero commutative normed ring is nonempty. -/
theorem nonempty_of_nontrivial [Nontrivial R] : Nonempty (Rigid.BerkovichSpectrum R) := by
  classical
  have hfinite (s : Finset R) :
      (Set.univ ∩ ⋂ c ∈ s, mulAt R c).Nonempty := by
    obtain ⟨p, hp⟩ := exists_mem_mulAt_finset R s
    refine ⟨p, ⟨Set.mem_univ p, ?_⟩⟩
    simp only [Set.mem_iInter]
    exact hp
  obtain ⟨p, _, hp⟩ := _root_.isCompact_univ.inter_iInter_nonempty (mulAt R)
    (isClosed_mulAt R) hfinite
  have hp_mul (c a : R) : p.toRingSeminorm (c * a) =
      p.toRingSeminorm c * p.toRingSeminorm a :=
    (Set.mem_iInter.mp hp c) a
  exact ⟨{
    seminorm :=
      { toFun := p.toRingSeminorm
        map_zero' := _root_.map_zero p.toRingSeminorm
        add_le' := map_add_le_add p.toRingSeminorm
        neg' := map_neg_eq_map p.toRingSeminorm
        map_one' := p.map_one
        map_mul' := hp_mul }
    le_norm' := fun a ↦ (p.1 a).2.2 }
  ⟩

/-- The Berkovich spectrum of a nonzero nonarchimedean commutative normed ring is nonempty. -/
theorem nonempty_of_isUltrametric [IsUltrametricDist R] [Nontrivial R] :
    Nonempty (Rigid.BerkovichSpectrum R) :=
  nonempty_of_nontrivial R

end

end Rigid.BerkovichSpectrum
