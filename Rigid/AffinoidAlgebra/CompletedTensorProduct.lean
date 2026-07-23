import Rigid.AffinoidAlgebra.AutomaticContinuity
import Rigid.TateAlgebra.PowerBoundedUniversalProperty

set_option linter.style.header false

/-!
# Completed tensor products of affinoid presentations

For chosen presentations of two strict affinoid algebras, their completed tensor product is
presented by putting both sets of variables into one Tate algebra and quotienting by the images of
the two presentation ideals. This file first records the presentation-level construction and its
two canonical algebra maps.
-/

universe u v w z

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {A : Type v} [CommRing A] [Algebra K A]
variable {B : Type w} [CommRing B] [Algebra K B]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Continuous algebra homomorphisms preserve power-bounded elements. -/
theorem isPowerBounded_map_continuousAlgHom
    {R : Type*} [NormedCommRing R] [NormedAlgebra K R]
    {S : Type*} [NormedCommRing S] [NormedAlgebra K S]
    (f : ContinuousAlgHom K R S) {x : R} (hx : IsPowerBounded x) :
    IsPowerBounded (f x) := by
  rcases hx with ⟨C, hC⟩
  refine ⟨‖f.toContinuousLinearMap‖ * max C 0, ?_⟩
  rintro _ ⟨m, rfl⟩
  change ‖f x ^ m‖ ≤ ‖f.toContinuousLinearMap‖ * max C 0
  rw [← map_pow]
  calc
    ‖f (x ^ m)‖ ≤ ‖f.toContinuousLinearMap‖ * ‖x ^ m‖ :=
      f.toContinuousLinearMap.le_opNorm (x ^ m)
    _ ≤ ‖f.toContinuousLinearMap‖ * max C 0 := by
      gcongr
      exact (hC ⟨m, rfl⟩).trans (le_max_left _ _)

namespace AffinoidPresentation

omit [CompleteSpace K] in
private theorem tateAlgebraQuotientMk_bijective (n : ℕ) :
    Function.Bijective
      (Ideal.Quotient.mkₐ K (⊥ : Ideal (TateAlgebra K (Fin n)))) :=
  ⟨by
    intro x y hxy
    apply sub_eq_zero.mp
    have hmem : x - y ∈ (⊥ : Ideal (TateAlgebra K (Fin n))) := by
      apply (Ideal.Quotient.eq_zero_iff_mem
        (I := (⊥ : Ideal (TateAlgebra K (Fin n)))) (a := x - y)).mp
      change Ideal.Quotient.mk (⊥ : Ideal (TateAlgebra K (Fin n))) x =
        Ideal.Quotient.mk (⊥ : Ideal (TateAlgebra K (Fin n))) y at hxy
      rw [map_sub, hxy, sub_self]
    exact hmem,
    Ideal.Quotient.mkₐ_surjective K ⊥⟩

private noncomputable def tateAlgebraQuotientEquiv (n : ℕ) :
    (TateAlgebra K (Fin n) ⧸ (⊥ : Ideal (TateAlgebra K (Fin n)))) ≃ₐ[K]
      TateAlgebra K (Fin n) :=
  (AlgEquiv.ofBijective (Ideal.Quotient.mkₐ K ⊥)
    (tateAlgebraQuotientMk_bijective K n)).symm

/-- The tautological presentation of a Tate algebra as the quotient by the zero ideal. -/
noncomputable def tateAlgebraPresentation (n : ℕ) :
    AffinoidPresentation K (TateAlgebra K (Fin n)) where
  n := n
  ideal := ⊥
  equiv := tateAlgebraQuotientEquiv K n

/-- A Tate algebra in finitely many variables is affinoid. -/
theorem tateAlgebra_isAffinoid (n : ℕ) :
    IsAffinoidAlgebra K (TateAlgebra K (Fin n)) :=
  ⟨tateAlgebraPresentation K n⟩

@[simp]
theorem tateAlgebraPresentation_toAlgHom (n : ℕ) :
    (tateAlgebraPresentation K n).toAlgHom = AlgHom.id K (TateAlgebra K (Fin n)) := by
  apply AlgHom.ext
  intro x
  change tateAlgebraQuotientEquiv K n (Ideal.Quotient.mk ⊥ x) = x
  exact (AlgEquiv.ofBijective (Ideal.Quotient.mkₐ K ⊥)
    (tateAlgebraQuotientMk_bijective K n)).symm_apply_apply x

/-- Algebra homomorphisms from a finite Tate algebra into an affinoid algebra are determined by
the Tate variables. Automatic continuity is essential here: this statement is false for arbitrary
algebraic targets. -/
theorem tateAlgebra_algHom_ext
    {C : Type z} [CommRing C] [Algebra K C] (n : ℕ)
    (R : AffinoidPresentation K C) (f g : TateAlgebra K (Fin n) →ₐ[K] C)
    (h : ∀ i, f (tateVariable K (Fin n) i) = g (tateVariable K (Fin n) i)) :
    f = g := by
  letI : NormedCommRing C := R.residueNormedCommRing K C
  letI : NormedAlgebra K C := R.residueNormedAlgebra K C
  letI : CompleteSpace C := R.residueCompleteSpace K C
  letI : IsUltrametricDist C := R.residueIsUltrametricDist K C
  let P := tateAlgebraPresentation K n
  let fc := P.continuousFromTate K R f
  let gc := P.continuousFromTate K R g
  have hx : ∀ i : Fin n, IsPowerBounded (fc (tateVariable K (Fin n) i)) := by
    intro i
    exact isPowerBounded_map_continuousAlgHom K fc
      (isPowerBounded_of_norm_le_one (norm_tateVariable K _ i).le)
  have hfg : fc = gc := by
    apply (existsUnique_continuousAlgHom_of_isPowerBounded (K := K) _ hx).unique
    · intro i
      rfl
    · intro i
      change g (AffinoidPresentation.toAlgHom K (TateAlgebra K (Fin n))
          (tateAlgebraPresentation K n)
          (tateVariable K (Fin n) i)) =
        f (AffinoidPresentation.toAlgHom K (TateAlgebra K (Fin n))
          (tateAlgebraPresentation K n) (tateVariable K (Fin n) i))
      rw [tateAlgebraPresentation_toAlgHom]
      exact (h i).symm
  apply (AlgHom.cancel_right (P.toAlgHom_surjective K _)).mp
  exact congrArg ContinuousAlgHom.toAlgHom hfg

/-- The continuous coordinate-block map from the left presentation. -/
noncomputable def leftBlockContinuousMap (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) :
    ContinuousAlgHom K (TateAlgebra K (Fin P.n)) (TateAlgebra K (Fin (P.n + Q.n))) :=
  TateAlgebra.eval K (Fin P.n)
    (fun i ↦ tateVariable K (Fin (P.n + Q.n)) (Fin.castAdd Q.n i))
    (fun _ ↦ (norm_tateVariable K _ _).le)

/-- The continuous coordinate-block map from the right presentation. -/
noncomputable def rightBlockContinuousMap (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) :
    ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) (TateAlgebra K (Fin (P.n + Q.n))) :=
  TateAlgebra.eval K (Fin Q.n)
    (fun i ↦ tateVariable K (Fin (P.n + Q.n)) (Fin.natAdd P.n i))
    (fun _ ↦ (norm_tateVariable K _ _).le)

/-- The coordinate-block map from the variables of the left presentation into the combined Tate
algebra. -/
noncomputable def leftBlockMap (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) :
    TateAlgebra K (Fin P.n) →ₐ[K] TateAlgebra K (Fin (P.n + Q.n)) :=
  (leftBlockContinuousMap K P Q).toAlgHom

/-- The coordinate-block map from the variables of the right presentation into the combined Tate
algebra. -/
noncomputable def rightBlockMap (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) :
    TateAlgebra K (Fin Q.n) →ₐ[K] TateAlgebra K (Fin (P.n + Q.n)) :=
  (rightBlockContinuousMap K P Q).toAlgHom

@[simp]
theorem leftBlockMap_tateVariable (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) (i : Fin P.n) :
    leftBlockMap K P Q (tateVariable K (Fin P.n) i) =
      tateVariable K (Fin (P.n + Q.n)) (Fin.castAdd Q.n i) :=
  by simp [leftBlockMap, leftBlockContinuousMap]

@[simp]
theorem rightBlockMap_tateVariable (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) (i : Fin Q.n) :
    rightBlockMap K P Q (tateVariable K (Fin Q.n) i) =
      tateVariable K (Fin (P.n + Q.n)) (Fin.natAdd P.n i) :=
  by simp [rightBlockMap, rightBlockContinuousMap]

/-- The ideal defining the completed tensor product of two chosen affinoid presentations. -/
noncomputable def completedTensorIdeal (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) : Ideal (TateAlgebra K (Fin (P.n + Q.n))) :=
  P.ideal.map (leftBlockMap K P Q) ⊔ Q.ideal.map (rightBlockMap K P Q)

/-- The completed tensor product associated with two chosen affinoid presentations. -/
noncomputable abbrev CompletedTensorProduct (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) : Type u :=
  TateAlgebra K (Fin (P.n + Q.n)) ⧸ completedTensorIdeal K P Q

noncomputable instance completedTensorProductCommRing (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) : CommRing (CompletedTensorProduct K P Q) :=
  inferInstance

noncomputable instance completedTensorProductAlgebra (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) : Algebra K (CompletedTensorProduct K P Q) :=
  inferInstance

/-- The chosen quotient presentation of the completed tensor product. -/
noncomputable def completedTensorPresentation (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) :
    AffinoidPresentation K (CompletedTensorProduct K P Q) where
  n := P.n + Q.n
  ideal := completedTensorIdeal K P Q
  equiv := AlgEquiv.refl

/-- A completed tensor product of two affinoid presentations is affinoid. -/
theorem completedTensorProduct_isAffinoid (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) :
    IsAffinoidAlgebra K (CompletedTensorProduct K P Q) :=
  ⟨completedTensorPresentation K P Q⟩

private theorem leftBlockMap_mem_completedTensorIdeal (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) {x : TateAlgebra K (Fin P.n)} (hx : x ∈ P.ideal) :
    leftBlockMap K P Q x ∈ completedTensorIdeal K P Q :=
  (show P.ideal.map (leftBlockMap K P Q) ≤ completedTensorIdeal K P Q from le_sup_left)
    (Ideal.mem_map_of_mem (leftBlockMap K P Q) hx)

private theorem rightBlockMap_mem_completedTensorIdeal (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) {x : TateAlgebra K (Fin Q.n)} (hx : x ∈ Q.ideal) :
    rightBlockMap K P Q x ∈ completedTensorIdeal K P Q :=
  (show Q.ideal.map (rightBlockMap K P Q) ≤ completedTensorIdeal K P Q from le_sup_right)
    (Ideal.mem_map_of_mem (rightBlockMap K P Q) hx)

/-- The canonical algebra map from the left affinoid algebra into the completed tensor product. -/
noncomputable def includeLeft (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) : A →ₐ[K] CompletedTensorProduct K P Q :=
  (Ideal.Quotient.liftₐ P.ideal
    ((Ideal.Quotient.mkₐ K (completedTensorIdeal K P Q)).comp (leftBlockMap K P Q))
    (fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr
      (leftBlockMap_mem_completedTensorIdeal K P Q hx))).comp P.equiv.symm.toAlgHom

/-- The canonical algebra map from the right affinoid algebra into the completed tensor product. -/
noncomputable def includeRight (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) : B →ₐ[K] CompletedTensorProduct K P Q :=
  (Ideal.Quotient.liftₐ Q.ideal
    ((Ideal.Quotient.mkₐ K (completedTensorIdeal K P Q)).comp (rightBlockMap K P Q))
    (fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr
      (rightBlockMap_mem_completedTensorIdeal K P Q hx))).comp Q.equiv.symm.toAlgHom

@[simp]
theorem includeLeft_toAlgHom (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) (a : TateAlgebra K (Fin P.n)) :
    includeLeft K P Q (AffinoidPresentation.toAlgHom K A P a) =
      Ideal.Quotient.mk (completedTensorIdeal K P Q) (leftBlockMap K P Q a) := by
  simp [includeLeft, AffinoidPresentation.toAlgHom]

@[simp]
theorem includeRight_toAlgHom (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) (b : TateAlgebra K (Fin Q.n)) :
    includeRight K P Q (AffinoidPresentation.toAlgHom K B Q b) =
      Ideal.Quotient.mk (completedTensorIdeal K P Q) (rightBlockMap K P Q b) := by
  simp [includeRight, AffinoidPresentation.toAlgHom]

theorem includeLeft_comp_toAlgHom (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) :
    (includeLeft K P Q).comp (AffinoidPresentation.toAlgHom K A P) =
      (Ideal.Quotient.mkₐ K (completedTensorIdeal K P Q)).comp (leftBlockMap K P Q) := by
  ext a
  exact includeLeft_toAlgHom K P Q a

theorem includeRight_comp_toAlgHom (P : AffinoidPresentation K A)
    (Q : AffinoidPresentation K B) :
    (includeRight K P Q).comp (AffinoidPresentation.toAlgHom K B Q) =
      (Ideal.Quotient.mkₐ K (completedTensorIdeal K P Q)).comp (rightBlockMap K P Q) := by
  ext b
  exact includeRight_toAlgHom K P Q b

private noncomputable def combinedPoint
    {C : Type z} [NormedCommRing C] [NormedAlgebra K C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (fc : ContinuousAlgHom K (TateAlgebra K (Fin P.n)) C)
    (gc : ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) C) :
    Fin (P.n + Q.n) → C :=
  Fin.addCases
    (fun i ↦ fc (tateVariable K (Fin P.n) i))
    (fun i ↦ gc (tateVariable K (Fin Q.n) i))

private theorem combinedPoint_isPowerBounded
    {C : Type z} [NormedCommRing C] [NormedAlgebra K C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (fc : ContinuousAlgHom K (TateAlgebra K (Fin P.n)) C)
    (gc : ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) C) :
    ∀ i, IsPowerBounded (combinedPoint K P Q fc gc i) := by
  intro i
  refine Fin.addCases
    (motive := fun i ↦ IsPowerBounded (combinedPoint K P Q fc gc i)) ?_ ?_ i
  · intro j
    simpa [combinedPoint] using isPowerBounded_map_continuousAlgHom K fc
      (isPowerBounded_of_norm_le_one (norm_tateVariable K _ j).le)
  · intro j
    simpa [combinedPoint] using isPowerBounded_map_continuousAlgHom K gc
      (isPowerBounded_of_norm_le_one (norm_tateVariable K _ j).le)

private noncomputable def combinedContinuousMap
    {C : Type z} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    [IsUltrametricDist C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (fc : ContinuousAlgHom K (TateAlgebra K (Fin P.n)) C)
    (gc : ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) C) :
    ContinuousAlgHom K (TateAlgebra K (Fin (P.n + Q.n))) C :=
  Classical.choose
    (existsUnique_continuousAlgHom_of_isPowerBounded (K := K)
      (combinedPoint K P Q fc gc) (combinedPoint_isPowerBounded K P Q fc gc)).exists

@[simp]
private theorem combinedContinuousMap_tateVariable
    {C : Type z} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    [IsUltrametricDist C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (fc : ContinuousAlgHom K (TateAlgebra K (Fin P.n)) C)
    (gc : ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) C)
    (i : Fin (P.n + Q.n)) :
    combinedContinuousMap K P Q fc gc (tateVariable K _ i) =
      combinedPoint K P Q fc gc i :=
  Classical.choose_spec
    (existsUnique_continuousAlgHom_of_isPowerBounded (K := K)
      (combinedPoint K P Q fc gc) (combinedPoint_isPowerBounded K P Q fc gc)).exists i

private theorem combinedContinuousMap_comp_left
    {C : Type z} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    [IsUltrametricDist C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (fc : ContinuousAlgHom K (TateAlgebra K (Fin P.n)) C)
    (gc : ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) C) :
    (combinedContinuousMap K P Q fc gc).comp (leftBlockContinuousMap K P Q) = fc := by
  apply (existsUnique_continuousAlgHom_of_isPowerBounded (K := K) _
    (fun i ↦ isPowerBounded_map_continuousAlgHom K fc
      (isPowerBounded_of_norm_le_one (norm_tateVariable K _ i).le))).unique
  · intro i
    simp [leftBlockContinuousMap, combinedPoint]
  · intro i
    rfl

private theorem combinedContinuousMap_comp_right
    {C : Type z} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    [IsUltrametricDist C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (fc : ContinuousAlgHom K (TateAlgebra K (Fin P.n)) C)
    (gc : ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) C) :
    (combinedContinuousMap K P Q fc gc).comp (rightBlockContinuousMap K P Q) = gc := by
  apply (existsUnique_continuousAlgHom_of_isPowerBounded (K := K) _
    (fun i ↦ isPowerBounded_map_continuousAlgHom K gc
      (isPowerBounded_of_norm_le_one (norm_tateVariable K _ i).le))).unique
  · intro i
    simp [rightBlockContinuousMap, combinedPoint]
  · intro i
    rfl

private theorem completedTensorIdeal_le_ker_combinedContinuousMap
    {C : Type z} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    [IsUltrametricDist C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (fc : ContinuousAlgHom K (TateAlgebra K (Fin P.n)) C)
    (gc : ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) C)
    (hfc : ∀ a ∈ P.ideal, fc a = 0) (hgc : ∀ b ∈ Q.ideal, gc b = 0) :
    completedTensorIdeal K P Q ≤
      RingHom.ker (combinedContinuousMap K P Q fc gc).toRingHom := by
  let φ := combinedContinuousMap K P Q fc gc
  rw [completedTensorIdeal, sup_le_iff]
  constructor
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change φ (leftBlockMap K P Q a) = 0
    change (φ.comp (leftBlockContinuousMap K P Q)) a = 0
    rw [combinedContinuousMap_comp_left K P Q fc gc]
    exact hfc a ha
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change φ (rightBlockMap K P Q b) = 0
    change (φ.comp (rightBlockContinuousMap K P Q)) b = 0
    rw [combinedContinuousMap_comp_right K P Q fc gc]
    exact hgc b hb

private noncomputable def completedTensorLiftOfContinuous
    {C : Type z} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    [IsUltrametricDist C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (fc : ContinuousAlgHom K (TateAlgebra K (Fin P.n)) C)
    (gc : ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) C)
    (hfc : ∀ a ∈ P.ideal, fc a = 0) (hgc : ∀ b ∈ Q.ideal, gc b = 0) :
    CompletedTensorProduct K P Q →ₐ[K] C :=
  Ideal.Quotient.liftₐ (completedTensorIdeal K P Q)
    (combinedContinuousMap K P Q fc gc).toAlgHom
    (completedTensorIdeal_le_ker_combinedContinuousMap K P Q fc gc hfc hgc)

private theorem completedTensorLiftOfContinuous_comp_leftBlock
    {C : Type z} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    [IsUltrametricDist C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (fc : ContinuousAlgHom K (TateAlgebra K (Fin P.n)) C)
    (gc : ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) C)
    (hfc : ∀ a ∈ P.ideal, fc a = 0) (hgc : ∀ b ∈ Q.ideal, gc b = 0) :
    (completedTensorLiftOfContinuous K P Q fc gc hfc hgc).comp
        ((Ideal.Quotient.mkₐ K (completedTensorIdeal K P Q)).comp (leftBlockMap K P Q)) =
      fc.toAlgHom := by
  rw [completedTensorLiftOfContinuous, ← AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
  exact congrArg ContinuousAlgHom.toAlgHom (combinedContinuousMap_comp_left K P Q fc gc)

private theorem completedTensorLiftOfContinuous_comp_rightBlock
    {C : Type z} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    [IsUltrametricDist C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (fc : ContinuousAlgHom K (TateAlgebra K (Fin P.n)) C)
    (gc : ContinuousAlgHom K (TateAlgebra K (Fin Q.n)) C)
    (hfc : ∀ a ∈ P.ideal, fc a = 0) (hgc : ∀ b ∈ Q.ideal, gc b = 0) :
    (completedTensorLiftOfContinuous K P Q fc gc hfc hgc).comp
        ((Ideal.Quotient.mkₐ K (completedTensorIdeal K P Q)).comp (rightBlockMap K P Q)) =
      gc.toAlgHom := by
  rw [completedTensorLiftOfContinuous, ← AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
  exact congrArg ContinuousAlgHom.toAlgHom (combinedContinuousMap_comp_right K P Q fc gc)

/-- The universal algebra map out of a completed tensor product into another affinoid algebra. -/
noncomputable def completedTensorLift
    {C : Type z} [CommRing C] [Algebra K C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (R : AffinoidPresentation K C) (f : A →ₐ[K] C) (g : B →ₐ[K] C) :
    CompletedTensorProduct K P Q →ₐ[K] C := by
  letI : NormedCommRing C := R.residueNormedCommRing K C
  letI : NormedAlgebra K C := R.residueNormedAlgebra K C
  letI : CompleteSpace C := R.residueCompleteSpace K C
  letI : IsUltrametricDist C := R.residueIsUltrametricDist K C
  let fc := P.continuousFromTate K R f
  let gc := Q.continuousFromTate K R g
  apply completedTensorLiftOfContinuous K P Q fc gc
  · intro a ha
    change f (AffinoidPresentation.toAlgHom K A P a) = 0
    have ha0 : AffinoidPresentation.toAlgHom K A P a = 0 := by
      change P.equiv (Ideal.Quotient.mk P.ideal a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    rw [ha0, map_zero]
  · intro b hb
    change g (AffinoidPresentation.toAlgHom K B Q b) = 0
    have hb0 : AffinoidPresentation.toAlgHom K B Q b = 0 := by
      change Q.equiv (Ideal.Quotient.mk Q.ideal b) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
    rw [hb0, map_zero]

theorem completedTensorLift_comp_includeLeft
    {C : Type z} [CommRing C] [Algebra K C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (R : AffinoidPresentation K C) (f : A →ₐ[K] C) (g : B →ₐ[K] C) :
    (completedTensorLift K P Q R f g).comp (includeLeft K P Q) = f := by
  apply (AlgHom.cancel_right (P.toAlgHom_surjective K A)).mp
  rw [AlgHom.comp_assoc, includeLeft_comp_toAlgHom K P Q]
  unfold completedTensorLift
  rw [completedTensorLiftOfContinuous_comp_leftBlock]
  rfl

theorem completedTensorLift_comp_includeRight
    {C : Type z} [CommRing C] [Algebra K C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (R : AffinoidPresentation K C) (f : A →ₐ[K] C) (g : B →ₐ[K] C) :
    (completedTensorLift K P Q R f g).comp (includeRight K P Q) = g := by
  apply (AlgHom.cancel_right (Q.toAlgHom_surjective K B)).mp
  rw [AlgHom.comp_assoc, includeRight_comp_toAlgHom K P Q]
  unfold completedTensorLift
  rw [completedTensorLiftOfContinuous_comp_rightBlock]
  rfl

/-- Algebra homomorphisms out of the completed tensor product are determined by their restrictions
to the two factors. -/
theorem completedTensorProduct_algHom_ext
    {C : Type z} [CommRing C] [Algebra K C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (R : AffinoidPresentation K C) (h₁ h₂ : CompletedTensorProduct K P Q →ₐ[K] C)
    (hleft : h₁.comp (includeLeft K P Q) = h₂.comp (includeLeft K P Q))
    (hright : h₁.comp (includeRight K P Q) = h₂.comp (includeRight K P Q)) :
    h₁ = h₂ := by
  letI : NormedCommRing C := R.residueNormedCommRing K C
  letI : NormedAlgebra K C := R.residueNormedAlgebra K C
  letI : CompleteSpace C := R.residueCompleteSpace K C
  letI : IsUltrametricDist C := R.residueIsUltrametricDist K C
  let S := completedTensorPresentation K P Q
  let h₁c := S.continuousFromTate K R h₁
  let h₂c := S.continuousFromTate K R h₂
  have hx : ∀ i : Fin (P.n + Q.n),
      IsPowerBounded (h₁c (tateVariable K (Fin (P.n + Q.n)) i)) := by
    intro i
    exact isPowerBounded_map_continuousAlgHom K h₁c
      (isPowerBounded_of_norm_le_one (norm_tateVariable K _ i).le)
  have hpoints : ∀ i : Fin (P.n + Q.n),
      h₂c (tateVariable K (Fin (P.n + Q.n)) i) =
        h₁c (tateVariable K (Fin (P.n + Q.n)) i) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      change h₂ (Ideal.Quotient.mk (completedTensorIdeal K P Q)
          (tateVariable K _ (Fin.castAdd Q.n j))) =
        h₁ (Ideal.Quotient.mk (completedTensorIdeal K P Q)
          (tateVariable K _ (Fin.castAdd Q.n j)))
      rw [← leftBlockMap_tateVariable K P Q j]
      rw [← includeLeft_toAlgHom K P Q (tateVariable K (Fin P.n) j)]
      change (h₂.comp (includeLeft K P Q))
          (AffinoidPresentation.toAlgHom K A P (tateVariable K (Fin P.n) j)) =
        (h₁.comp (includeLeft K P Q))
          (AffinoidPresentation.toAlgHom K A P (tateVariable K (Fin P.n) j))
      rw [hleft]
    · intro j
      change h₂ (Ideal.Quotient.mk (completedTensorIdeal K P Q)
          (tateVariable K _ (Fin.natAdd P.n j))) =
        h₁ (Ideal.Quotient.mk (completedTensorIdeal K P Q)
          (tateVariable K _ (Fin.natAdd P.n j)))
      rw [← rightBlockMap_tateVariable K P Q j]
      rw [← includeRight_toAlgHom K P Q (tateVariable K (Fin Q.n) j)]
      change (h₂.comp (includeRight K P Q))
          (AffinoidPresentation.toAlgHom K B Q (tateVariable K (Fin Q.n) j)) =
        (h₁.comp (includeRight K P Q))
          (AffinoidPresentation.toAlgHom K B Q (tateVariable K (Fin Q.n) j))
      rw [hright]
  have hc : h₂c = h₁c :=
    (existsUnique_continuousAlgHom_of_isPowerBounded (K := K) _ hx).unique hpoints
      (fun _ ↦ rfl)
  apply (AlgHom.cancel_right (S.toAlgHom_surjective K _)).mp
  exact (congrArg ContinuousAlgHom.toAlgHom hc).symm

/-- The completed tensor product has the coproduct universal property among affinoid algebras. -/
theorem existsUnique_algHom_from_completedTensorProduct
    {C : Type z} [CommRing C] [Algebra K C]
    (P : AffinoidPresentation K A) (Q : AffinoidPresentation K B)
    (R : AffinoidPresentation K C) (f : A →ₐ[K] C) (g : B →ₐ[K] C) :
    ∃! h : CompletedTensorProduct K P Q →ₐ[K] C,
      h.comp (includeLeft K P Q) = f ∧ h.comp (includeRight K P Q) = g := by
  refine ⟨completedTensorLift K P Q R f g,
    ⟨completedTensorLift_comp_includeLeft K P Q R f g,
      completedTensorLift_comp_includeRight K P Q R f g⟩, ?_⟩
  intro h hh
  apply completedTensorProduct_algHom_ext K P Q R
  · rw [hh.1, completedTensorLift_comp_includeLeft K P Q R f g]
  · rw [hh.2, completedTensorLift_comp_includeRight K P Q R f g]

end AffinoidPresentation

end Rigid
