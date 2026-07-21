import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Sum

set_option linter.style.header false

/-!
# Spectral smoothing for ordinary ring seminorms

Mathlib proves that the spectral smoothing function of a nonarchimedean ring seminorm is again a
nonarchimedean ring seminorm. This file proves the ordinary triangle inequality without assuming
that the original seminorm is nonarchimedean.

The main estimate splits powers into blocks of a fixed size. The fixed block is controlled by the
spectral radius, while the finitely many possible remainders contribute a constant whose `n`-th
root tends to one. The binomial theorem then gives subadditivity in the limit.
-/

open Filter Nat Real
open scoped Topology BigOperators

noncomputable section

namespace Rigid

variable {R : Type*} [CommRing R]

private theorem residue_pow_bound {u A : ℝ} (hu : 0 ≤ u) (hA : 0 < A) {r k : ℕ}
    (hrk : r ≤ k) :
    u ^ r ≤ max 1 ((u / A) ^ k) * A ^ r := by
  by_cases h : u ≤ A
  · calc
      u ^ r ≤ A ^ r := pow_le_pow_left₀ hu h r
      _ = 1 * A ^ r := by rw [one_mul]
      _ ≤ max 1 ((u / A) ^ k) * A ^ r := by
        gcongr
        exact le_max_left _ _
  · have hratio : 1 ≤ u / A := (le_div_iff₀ hA).2 (by simpa using le_of_not_ge h)
    calc
      u ^ r = (u / A) ^ r * A ^ r := by rw [← mul_pow, div_mul_cancel₀ u hA.ne']
      _ ≤ (u / A) ^ k * A ^ r := by gcongr
      _ ≤ max 1 ((u / A) ^ k) * A ^ r := by
        gcongr
        exact le_max_right _ _

private theorem map_natCast_le (μ : RingSeminorm R) (hμ1 : μ 1 ≤ 1) (n : ℕ) :
    μ (n : R) ≤ (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      exact (map_add_le_add μ (n : R) 1).trans (by simpa using add_le_add ih hμ1)

private theorem map_finset_sum_le (μ : RingSeminorm R) {ι : Type*} (s : Finset ι) (f : ι → R) :
    μ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, μ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (map_add_le_add μ (f a) (∑ i ∈ s, f i)).trans (add_le_add_right ih _)

private theorem map_pow_le_const_mul_pow (μ : RingSeminorm R) (hμ1 : μ 1 ≤ 1)
    {x : R} {A : ℝ} (hA : 0 < A) {k : ℕ} (hk : 0 < k)
    (hxk : μ (x ^ k) ≤ A ^ k) (i : ℕ) :
    μ (x ^ i) ≤ max 1 ((μ x / A) ^ k) * A ^ i := by
  let q := i / k
  let r := i % k
  have hrk : r ≤ k := (Nat.mod_lt i hk).le
  have hpow : μ (x ^ i) ≤ μ (x ^ k) ^ q * μ x ^ r := by
    rw [← Nat.div_add_mod i k, pow_add, pow_mul]
    exact (map_mul_le_mul μ ((x ^ k) ^ q) (x ^ r)).trans
      (mul_le_mul (map_pow_le_pow' hμ1 (x ^ k) q) (map_pow_le_pow' hμ1 x r)
        (apply_nonneg μ _) (pow_nonneg (apply_nonneg μ _) _))
  calc
    μ (x ^ i) ≤ μ (x ^ k) ^ q * μ x ^ r := hpow
    _ ≤ (A ^ k) ^ q * μ x ^ r := by gcongr
    _ ≤ (A ^ k) ^ q * (max 1 ((μ x / A) ^ k) * A ^ r) := by
      gcongr
      exact residue_pow_bound (apply_nonneg μ x) hA hrk
    _ = max 1 ((μ x / A) ^ k) * A ^ i := by
      rw [← Nat.div_add_mod i k, pow_add, pow_mul]
      ring

/-- The spectral smoothing function of a ring seminorm with `μ 1 ≤ 1` is subadditive. -/
theorem smoothingFun_add_le (μ : RingSeminorm R) (hμ1 : μ 1 ≤ 1) (x y : R) :
    smoothingFun μ (x + y) ≤ smoothingFun μ x + smoothingFun μ y := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := δ / 2
  let A := smoothingFun μ x + ε
  let B := smoothingFun μ y + ε
  have hε : 0 < ε := half_pos hδ
  have hA : 0 < A := add_pos_of_nonneg_of_pos (smoothingFun_nonneg μ hμ1 x) hε
  have hB : 0 < B := add_pos_of_nonneg_of_pos (smoothingFun_nonneg μ hμ1 y) hε
  have hxev : ∀ᶠ n : ℕ in atTop, smoothingSeminormSeq μ x n < A :=
    (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x) (Iio_mem_nhds (by simp [A, hε]))
  have hyev : ∀ᶠ n : ℕ in atTop, smoothingSeminormSeq μ y n < B :=
    (tendsto_smoothingFun_of_map_one_le_one μ hμ1 y) (Iio_mem_nhds (by simp [B, hε]))
  obtain ⟨k, hxroot, hyroot, hk⟩ :=
    (hxev.and (hyev.and (show ∀ᶠ n : ℕ in atTop, 1 ≤ n from eventually_ge_atTop 1))).exists
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (one_le_iff_ne_zero.mp hk)
  have hxk : μ (x ^ k) ≤ A ^ k := by
    calc
      μ (x ^ k) = (μ (x ^ k) ^ (1 / (k : ℝ))) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (apply_nonneg μ _), one_div_mul_cancel hk0,
          Real.rpow_one]
      _ ≤ A ^ k := pow_le_pow_left₀ (Real.rpow_nonneg (apply_nonneg μ _) _) hxroot.le k
  have hyk : μ (y ^ k) ≤ B ^ k := by
    calc
      μ (y ^ k) = (μ (y ^ k) ^ (1 / (k : ℝ))) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (apply_nonneg μ _), one_div_mul_cancel hk0,
          Real.rpow_one]
      _ ≤ B ^ k := pow_le_pow_left₀ (Real.rpow_nonneg (apply_nonneg μ _) _) hyroot.le k
  let Cx := max 1 ((μ x / A) ^ k)
  let Cy := max 1 ((μ y / B) ^ k)
  let C := Cx * Cy
  have hC : 0 < C := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hbinomial (n : ℕ) : μ ((x + y) ^ n) ≤ C * (A + B) ^ n := by
    rw [add_pow]
    calc
      μ (∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i) * (n.choose i : R)) ≤
          ∑ i ∈ Finset.range (n + 1), μ (x ^ i * y ^ (n - i) * (n.choose i : R)) :=
        map_finset_sum_le μ _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          C * (A ^ i * B ^ (n - i) * (n.choose i : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          μ (x ^ i * y ^ (n - i) * (n.choose i : R)) ≤
              (μ (x ^ i) * μ (y ^ (n - i))) * μ (n.choose i : R) :=
            (map_mul_le_mul μ _ _).trans <| mul_le_mul_of_nonneg_right
              (map_mul_le_mul μ _ _) (apply_nonneg μ _)
          _ ≤ (Cx * A ^ i * (Cy * B ^ (n - i))) * (n.choose i : ℝ) := by
            gcongr
            · exact map_pow_le_const_mul_pow μ hμ1 hA hk hxk i
            · exact map_pow_le_const_mul_pow μ hμ1 hB hk hyk (n - i)
            · exact map_natCast_le μ hμ1 _
          _ = C * (A ^ i * B ^ (n - i) * (n.choose i : ℝ)) := by
            simp only [C]
            ring
      _ = C * (A + B) ^ n := by
        rw [add_pow, Finset.mul_sum]
  have hroot : ∀ᶠ n : ℕ in atTop,
      smoothingSeminormSeq μ (x + y) n ≤ C ^ (1 / (n : ℝ)) * (A + B) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    calc
      μ ((x + y) ^ n) ^ (1 / (n : ℝ)) ≤ (C * (A + B) ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (apply_nonneg μ _) (hbinomial n) (by positivity)
      _ = C ^ (1 / (n : ℝ)) * (A + B) := by
        rw [Real.mul_rpow hC.le (pow_nonneg (add_nonneg hA.le hB.le) n)]
        congr 1
        simpa only [one_div] using
          Real.pow_rpow_inv_natCast (add_nonneg hA.le hB.le) (one_le_iff_ne_zero.mp hn)
  have hCroot : Tendsto (fun n : ℕ ↦ C ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    convert tendsto_const_nhds.rpow tendsto_one_div_atTop_nhds_zero_nat (Or.inl hC.ne') using 1
    rw [Real.rpow_zero]
  have hle : smoothingFun μ (x + y) ≤ A + B :=
    le_of_tendsto_of_tendsto (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x + y))
      (by simpa using hCroot.mul_const (A + B)) hroot
  dsimp only [A, B, ε] at hle
  linarith

/-- The spectral smoothing function bundled as a power-multiplicative ring seminorm. -/
def spectralSmoothingSeminorm (μ : RingSeminorm R) (hμ1 : μ 1 ≤ 1) : RingSeminorm R where
  toFun := smoothingFun μ
  map_zero' := by
    apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 0)
      tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [smoothingSeminormSeq, zero_pow (one_le_iff_ne_zero.mp hn), map_zero]
    rw [zero_rpow (one_div_cast_ne_zero (one_le_iff_ne_zero.mp hn))]
  add_le' := smoothingFun_add_le μ hμ1
  neg' n := by
    simp only [smoothingFun]
    congr
    ext k
    rw [neg_pow]
    rcases neg_one_pow_eq_or R k with hpos | hneg
    · rw [hpos, one_mul]
    · rw [hneg, neg_one_mul, map_neg_eq_map μ]
  mul_le' x y := by
    apply le_of_tendsto_of_tendsto' (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x * y))
      (Tendsto.mul (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
        (tendsto_smoothingFun_of_map_one_le_one μ hμ1 y))
    intro n
    have hn : 0 ≤ 1 / (n : ℝ) := by positivity
    simp only [smoothingSeminormSeq]
    rw [← mul_rpow (apply_nonneg μ _) (apply_nonneg μ _), mul_pow]
    gcongr
    exact map_mul_le_mul μ _ _

/-- Spectral smoothing is power-multiplicative. -/
theorem isPowMul_spectralSmoothingSeminorm (μ : RingSeminorm R) (hμ1 : μ 1 ≤ 1) :
    IsPowMul (spectralSmoothingSeminorm μ hμ1) :=
  isPowMul_smoothingFun μ hμ1

/-- Spectral smoothing does not increase a ring seminorm. -/
theorem spectralSmoothingSeminorm_le (μ : RingSeminorm R) (hμ1 : μ 1 ≤ 1) (x : R) :
    spectralSmoothingSeminorm μ hμ1 x ≤ μ x :=
  smoothingFun_le_self μ x

end Rigid
