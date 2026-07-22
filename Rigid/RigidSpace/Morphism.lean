import Rigid.RigidSpace.Basic

set_option linter.style.header false

/-!
# Analytic morphisms of rigid spaces

The production morphism type is the locally ringed-space morphism from `Basic`: it contains the
map on points, inverse images of admissible opens, pullback maps on analytic sections, and local
maps on stalks. This module gives that data its public analytic-morphism name. In particular,
the public production API never identifies a morphism with an arbitrary function on points.
-/

universe u

namespace Rigid

open CategoryTheory

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

namespace RigidSpace

/-- The locally ringed-space data of an analytic morphism.

This is an alias for `Hom`; the fields are therefore the map on points, inverse-image operation on
admissible opens, pullback on sections, and local maps on stalks together with their compatibility
laws.
-/
abbrev AnalyticMorphismData (X Y : RigidSpace K) : Type (u + 1) := Hom K X Y

namespace AnalyticMorphismData

/-- Identity analytic morphism. -/
noncomputable abbrev id (X : RigidSpace K) : AnalyticMorphismData K X X := Hom.id K X

/-- Composition of analytic morphisms. -/
noncomputable abbrev comp {X Y Z : RigidSpace K}
    (f : AnalyticMorphismData K X Y) (g : AnalyticMorphismData K Y Z) :
    AnalyticMorphismData K X Z := Hom.comp K f g

@[simp]
theorem id_base (X : RigidSpace K) : (id K X).base = _root_.id := by
  rfl

@[simp]
theorem id_preimage (X : RigidSpace K) (U : X.admissibleTopology.Open) :
    (id K X).preimage U = U := by
  rfl

@[simp]
theorem comp_base {X Y Z : RigidSpace K}
    (f : AnalyticMorphismData K X Y) (g : AnalyticMorphismData K Y Z) :
    (comp K f g).base = g.base ∘ f.base := by
  rfl

@[simp]
theorem comp_preimage {X Y Z : RigidSpace K}
    (f : AnalyticMorphismData K X Y) (g : AnalyticMorphismData K Y Z)
    (U : Z.admissibleTopology.Open) :
    (comp K f g).preimage U = f.preimage (g.preimage U) := by
  rfl

end AnalyticMorphismData

/-- The analytic-morphism data associated with a locally ringed-space morphism. -/
noncomputable def analyticHomEquiv (X Y : RigidSpace K) :
    (X ⟶ Y) ≃ AnalyticMorphismData K X Y := Equiv.refl _

@[simp]
theorem analyticHomEquiv_base {X Y : RigidSpace K} (f : X ⟶ Y) :
    (analyticHomEquiv K X Y f).base = f.base := rfl

@[simp]
theorem analyticHomEquiv_id (X : RigidSpace K) :
    analyticHomEquiv K X X (𝟙 X) = AnalyticMorphismData.id K X := rfl

@[simp]
theorem analyticHomEquiv_comp {X Y Z : RigidSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    analyticHomEquiv K X Z (f ≫ g) =
      AnalyticMorphismData.comp K (analyticHomEquiv K X Y f)
        (analyticHomEquiv K Y Z g) := rfl

end RigidSpace

end Rigid
