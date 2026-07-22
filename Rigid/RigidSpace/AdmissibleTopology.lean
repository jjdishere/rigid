import Mathlib

set_option linter.style.header false

/-!
# Tate admissible topologies

An admissible topology is the point-set presentation of the Grothendieck topology used in Tate
rigid geometry. Its admissible opens are a distinguished collection of subsets, closed under the
full space and binary intersections. Admissible coverings are additional data: a set-theoretic
cover need not be admissible.

The covering axioms below are the covering-family form of the Grothendieck-topology axioms. In
particular, `transitive` includes saturation under refinement, which makes the notion independent
of repetitions or reindexing in a covering family.
-/

universe u v w

namespace Rigid

/-- A Tate admissible topology on a type of analytic points. -/
structure AdmissibleTopology (X : Type u) where
  /-- The distinguished point subsets that are admissible opens. -/
  IsOpen : Set X → Prop
  /-- The full point set is admissible. -/
  isOpen_univ : IsOpen Set.univ
  /-- Binary intersections of admissible opens are admissible. -/
  isOpen_inter {U V : Set X} : IsOpen U → IsOpen V → IsOpen (U ∩ V)
  /-- The admissible covering relation. A cover is represented by the set of its members, so it is
  invariant under reindexing and repetition. -/
  Covers : Set (Set X) → Set X → Prop
  /-- A cover consists of admissible opens and has an admissible target. -/
  covers_isOpen {U : Set X} {family : Set (Set X)} :
    Covers family U → IsOpen U ∧ ∀ V ∈ family, IsOpen V
  /-- Every member of a cover lies in its target. -/
  covers_subset {U : Set X} {family : Set (Set X)} :
    Covers family U → ∀ V ∈ family, V ⊆ U
  /-- An admissible cover covers the target point set. -/
  covers_sUnion {U : Set X} {family : Set (Set X)} :
    Covers family U → U = ⋃₀ family
  /-- The singleton family is an admissible cover. -/
  singleton {U : Set X} : IsOpen U → Covers {U} U
  /-- Admissible covers are stable under intersection with an admissible open. -/
  pullback {U W : Set X} {family : Set (Set X)} :
    Covers family U → IsOpen W → Covers ((fun V ↦ V ∩ W) '' family) (U ∩ W)
  /-- Coverings are transitive and saturated under admissible refinements. -/
  transitive {U : Set X} {family refinement : Set (Set X)} :
    Covers family U →
      (∀ V ∈ family, ∃ subcover, Covers subcover V ∧ subcover ⊆ refinement) →
      (∀ W ∈ refinement, IsOpen W ∧ W ⊆ U) → Covers refinement U

namespace AdmissibleTopology

/-- The fine admissible topology, in which every subset is admissible and the admissible covers
are exactly the set-theoretic covers by subsets of the target. -/
def fine (X : Type u) : AdmissibleTopology X where
  IsOpen := fun _ ↦ True
  isOpen_univ := trivial
  isOpen_inter := fun _ _ ↦ trivial
  Covers := fun family U ↦ (∀ V ∈ family, V ⊆ U) ∧ U = ⋃₀ family
  covers_isOpen h := ⟨trivial, fun _ _ ↦ trivial⟩
  covers_subset h := h.1
  covers_sUnion h := h.2
  singleton h := ⟨by simp, by simp⟩
  pullback {U W family} hU hW := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩ x ⟨hxV, hxW⟩
      exact ⟨hU.1 V hV hxV, hxW⟩
    · ext x
      constructor
      · rintro ⟨hxU, hxW⟩
        rw [hU.2] at hxU
        rcases hxU with ⟨V, hV, hxV⟩
        exact ⟨V ∩ W, ⟨V, hV, rfl⟩, hxV, hxW⟩
      · rintro ⟨_, ⟨V, hV, rfl⟩, hxV, hxW⟩
        exact ⟨hU.1 V hV hxV, hxW⟩
  transitive {U family refinement} hU hRefinement hOpen := by
    refine ⟨fun W hW ↦ (hOpen W hW).2, ?_⟩
    ext x
    constructor
    · intro hx
      rw [hU.2] at hx
      rcases hx with ⟨V, hV, hxV⟩
      obtain ⟨subcover, hSubcover, hSubcoverRefines⟩ := hRefinement V hV
      rw [hSubcover.2] at hxV
      rcases hxV with ⟨W, hW, hxW⟩
      exact ⟨W, hSubcoverRefines hW, hxW⟩
    · rintro ⟨W, hW, hxW⟩
      exact (hOpen W hW).2 hxW

variable {X : Type u} (T : AdmissibleTopology X)

/-- An admissible open is a point subset certified to belong to the admissible topology. -/
def Open := { U : Set X // T.IsOpen U }

namespace Open

instance : SetLike T.Open X where
  coe U := U.1
  coe_injective _ _ h := Subtype.ext h

instance : PartialOrder T.Open :=
  PartialOrder.ofSetLike T.Open X

@[simp]
theorem le_def (U V : T.Open) : U ≤ V ↔ (U : Set X) ⊆ (V : Set X) :=
  Iff.rfl

@[simp]
theorem mem_mk {U : Set X} (hU : T.IsOpen U) (x : X) :
    x ∈ ((⟨U, hU⟩ : T.Open) : Set X) ↔ x ∈ U :=
  Iff.rfl

/-- The full admissible open. -/
def top : T.Open :=
  ⟨Set.univ, T.isOpen_univ⟩

@[simp]
theorem coe_top : (top T : Set X) = Set.univ :=
  rfl

/-- The intersection of two admissible opens. -/
def inter (U V : T.Open) : T.Open :=
  ⟨(U : Set X) ∩ (V : Set X), T.isOpen_inter U.2 V.2⟩

@[simp]
theorem coe_inter (U V : T.Open) : (inter T U V : Set X) = (U : Set X) ∩ (V : Set X) :=
  rfl

@[ext]
theorem ext {U V : T.Open} (h : (U : Set X) = (V : Set X)) : U = V :=
  SetLike.coe_injective h

/-- A family of admissible opens is an admissible cover when its set of members covers the target
in the specified Tate admissible topology. -/
def IsCover {I : Type v} (U : I → T.Open) (V : T.Open) : Prop :=
  T.Covers (Set.range fun i ↦ (U i : Set X)) (V : Set X)

namespace IsCover

variable {T}

/-- A singleton-indexed family covers its member. -/
theorem singleton (V : T.Open) : IsCover T (fun _ : PUnit ↦ V) V := by
  change T.Covers (Set.range fun _ : PUnit ↦ (V : Set X)) (V : Set X)
  rw [show Set.range (fun _ : PUnit ↦ (V : Set X)) = {(V : Set X)} by ext W; simp]
  exact T.singleton V.2

private theorem range_inter {I : Type v} (U : I → T.Open) (W : T.Open) :
    Set.range (fun i ↦ (inter T (U i) W : Set X)) =
      (fun V : Set X ↦ V ∩ (W : Set X)) '' Set.range (fun i ↦ (U i : Set X)) := by
  ext V
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨U i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- Admissible covers are stable under intersection with another admissible open. -/
theorem pullback {I : Type v} {U : I → T.Open} {V : T.Open} (h : IsCover T U V)
    (W : T.Open) : IsCover T (fun i ↦ inter T (U i) W) (inter T V W) := by
  change T.Covers (Set.range fun i ↦ (inter T (U i) W : Set X))
    ((V : Set X) ∩ (W : Set X))
  rw [range_inter]
  exact T.pullback h W.2

/-- Admissible coverings are transitive. -/
theorem trans {I : Type v} {J : I → Type w} {U : I → T.Open} {V : T.Open}
    (hU : IsCover T U V) (W : ∀ i, J i → T.Open)
    (hW : ∀ i, IsCover T (W i) (U i)) :
    IsCover T (fun p : Σ i, J i ↦ W p.1 p.2) V := by
  apply T.transitive hU
  · rintro S ⟨i, rfl⟩
    refine ⟨Set.range (fun j ↦ (W i j : Set X)), hW i, ?_⟩
    rintro R ⟨j, rfl⟩
    exact ⟨⟨i, j⟩, rfl⟩
  · rintro R ⟨⟨i, j⟩, rfl⟩
    exact ⟨(T.covers_isOpen (hW i)).2 _ ⟨j, rfl⟩,
      ((T.covers_subset (hW i)) _ ⟨j, rfl⟩).trans
        ((T.covers_subset hU) _ ⟨i, rfl⟩)⟩

/-- Every member of an admissible cover is contained in its target. -/
theorem subset {I : Type v} {U : I → T.Open} {V : T.Open} (h : IsCover T U V) (i : I) :
    (U i : Set X) ⊆ (V : Set X) :=
  T.covers_subset h _ ⟨i, rfl⟩

/-- An admissible cover covers the underlying point set. -/
theorem iUnion {I : Type v} {U : I → T.Open} {V : T.Open} (h : IsCover T U V) :
    (V : Set X) = ⋃ i, (U i : Set X) := by
  rw [T.covers_sUnion h, Set.sUnion_range]

end IsCover

end Open

end AdmissibleTopology

end Rigid
