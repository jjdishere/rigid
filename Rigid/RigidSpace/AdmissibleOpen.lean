import Rigid.RigidSpace.Basic

set_option linter.style.header false

/-!
# Admissible opens of a rigid space

This module specializes Tate admissible topologies to the analytic points of a rigid space and
records the covering and quasi-compactness API used by the global theory.
-/

universe u

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

namespace RigidSpace

/-- An admissible open of a rigid space. -/
abbrev AdmissibleOpen (X : RigidSpace K) : Type (u + 1) :=
  ULift.{u + 1, u} X.admissibleTopology.Open

namespace AdmissibleOpen

/-- The analytic points belonging to an admissible open. -/
def carrier {X : RigidSpace K} (U : AdmissibleOpen K X) : Set (Point K X) :=
  {x | x.down ∈ (U.down : Set X.points)}

/-- Admissible opens are determined by their point sets. -/
@[ext]
theorem ext {X : RigidSpace K} {U V : AdmissibleOpen K X} (h : U.carrier = V.carrier) : U = V :=
  by
    apply ULift.ext
    apply AdmissibleTopology.Open.ext X.admissibleTopology
    ext x
    exact Set.ext_iff.mp h ⟨x⟩

/-- The full admissible open. -/
def top (X : RigidSpace K) : AdmissibleOpen K X :=
  ⟨AdmissibleTopology.Open.top X.admissibleTopology⟩

@[simp]
theorem carrier_top (X : RigidSpace K) : (top K X).carrier = Set.univ :=
  by ext; rfl

/-- The intersection of two admissible opens. -/
def inter {X : RigidSpace K} (U V : AdmissibleOpen K X) : AdmissibleOpen K X :=
  ⟨AdmissibleTopology.Open.inter X.admissibleTopology U.down V.down⟩

@[simp]
theorem carrier_inter {X : RigidSpace K} (U V : AdmissibleOpen K X) :
    (inter K U V).carrier = U.carrier ∩ V.carrier :=
  by ext; rfl

/-- The intersection is contained in its left factor. -/
theorem inter_subset_left {X : RigidSpace K} (U V : AdmissibleOpen K X) :
    (inter K U V).carrier ⊆ U.carrier :=
  Set.inter_subset_left

/-- The intersection is contained in its right factor. -/
theorem inter_subset_right {X : RigidSpace K} (U V : AdmissibleOpen K X) :
    (inter K U V).carrier ⊆ V.carrier :=
  Set.inter_subset_right

/-- A family is an admissible cover of an admissible open in the rigid Grothendieck topology. -/
abbrev IsCover {X : RigidSpace K} {ι : Type (u + 1)}
    (U : ι → AdmissibleOpen K X) (V : AdmissibleOpen K X) : Prop :=
  AdmissibleTopology.Open.IsCover X.admissibleTopology (fun i ↦ (U i).down) V.down

namespace IsCover

/-- A one-member family covers its member. -/
theorem singleton {X : RigidSpace K} (V : AdmissibleOpen K X) :
    IsCover K (fun _ : PUnit ↦ V) V :=
  AdmissibleTopology.Open.IsCover.singleton V.down

/-- Admissible covers are stable under intersection with another admissible open. -/
theorem pullback {X : RigidSpace K} {ι : Type (u + 1)}
    {U : ι → AdmissibleOpen K X} {V : AdmissibleOpen K X} (h : IsCover K U V)
    (W : AdmissibleOpen K X) :
    IsCover K (fun i ↦ inter K (U i) W) (inter K V W) :=
  AdmissibleTopology.Open.IsCover.pullback h W.down

/-- Admissible coverings are transitive. -/
theorem trans {X : RigidSpace K} {ι : Type (u + 1)} {κ : ι → Type (u + 1)}
    {U : ι → AdmissibleOpen K X} {V : AdmissibleOpen K X} (hU : IsCover K U V)
    (W : ∀ i, κ i → AdmissibleOpen K X) (hW : ∀ i, IsCover K (W i) (U i)) :
    IsCover K (fun p : Σ i, κ i ↦ W p.1 p.2) V :=
  AdmissibleTopology.Open.IsCover.trans hU (fun i j ↦ (W i j).down) hW

/-- Every member of an admissible cover is contained in the covered open. -/
theorem subset {X : RigidSpace K} {ι : Type (u + 1)}
    {U : ι → AdmissibleOpen K X} {V : AdmissibleOpen K X} (h : IsCover K U V) (i : ι) :
    (U i).carrier ⊆ V.carrier :=
  by
    intro x hx
    exact AdmissibleTopology.Open.IsCover.subset h i hx

/-- An admissible cover covers the underlying point set. -/
theorem iUnion_carrier {X : RigidSpace K} {ι : Type (u + 1)}
    {U : ι → AdmissibleOpen K X} {V : AdmissibleOpen K X} (h : IsCover K U V) :
    V.carrier = ⋃ i, (U i).carrier :=
  by
    ext x
    rw [Set.mem_iUnion]
    change x.down ∈ (V.down : Set X.points) ↔ ∃ i, x.down ∈ ((U i).down : Set X.points)
    simpa only [Set.mem_iUnion] using
      Set.ext_iff.mp (AdmissibleTopology.Open.IsCover.iUnion h) x.down

end IsCover

/-- An admissible open is quasi-compact for the admissible topology. -/
def IsQuasiCompact {X : RigidSpace K} (U : AdmissibleOpen K X) : Prop :=
  ∀ {ι : Type (u + 1)} (V : ι → AdmissibleOpen K X), IsCover K V U →
    ∃ s : Set ι, s.Finite ∧ IsCover K (fun i : s ↦ V i.1) U

/-- Quasi-compactness means that every admissible cover has a finite admissible subcover. -/
theorem isQuasiCompact_iff {X : RigidSpace K} (U : AdmissibleOpen K X) :
    IsQuasiCompact K U ↔
      ∀ {ι : Type (u + 1)} (V : ι → AdmissibleOpen K X), IsCover K V U →
        ∃ s : Set ι, s.Finite ∧ IsCover K (fun i : s ↦ V i.1) U :=
  Iff.rfl

end AdmissibleOpen

end RigidSpace

end Rigid
