import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Rigid.AffinoidAlgebra.CompletedTensorProduct

set_option linter.style.header false

/-!
# The category of strict affinoid algebras

Strict affinoid algebras with algebra homomorphisms form a category. Chosen quotient
presentations construct binary coproducts by completed tensor product. Consequently, the opposite
category, which is the local algebraic model for affinoid spectra, has binary products.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- A strict affinoid `K`-algebra bundled with its algebraic structure. -/
structure AffinoidAlgebraCat where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra K carrier]
  isAffinoid : IsAffinoidAlgebra K carrier

attribute [instance] AffinoidAlgebraCat.commRing AffinoidAlgebraCat.algebra

instance : CoeSort (AffinoidAlgebraCat K) (Type u) :=
  ⟨AffinoidAlgebraCat.carrier⟩

namespace AffinoidAlgebraCat

/-- Morphisms of strict affinoid algebras are `K`-algebra homomorphisms. -/
abbrev Hom (A B : AffinoidAlgebraCat K) := A →ₐ[K] B

instance category : Category (AffinoidAlgebraCat K) where
  Hom := Hom K
  id A := AlgHom.id K A
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace Coproduct

/-- The completed tensor product object associated with the chosen presentations of `A` and `B`. -/
noncomputable def obj (A B : AffinoidAlgebraCat K) : AffinoidAlgebraCat K where
  carrier := AffinoidPresentation.CompletedTensorProduct K
    A.isAffinoid.presentation B.isAffinoid.presentation
  isAffinoid := AffinoidPresentation.completedTensorProduct_isAffinoid K
    A.isAffinoid.presentation B.isAffinoid.presentation

/-- The left coproduct inclusion. -/
noncomputable def inl (A B : AffinoidAlgebraCat K) : A ⟶ obj K A B :=
  AffinoidPresentation.includeLeft K A.isAffinoid.presentation B.isAffinoid.presentation

/-- The right coproduct inclusion. -/
noncomputable def inr (A B : AffinoidAlgebraCat K) : B ⟶ obj K A B :=
  AffinoidPresentation.includeRight K A.isAffinoid.presentation B.isAffinoid.presentation

/-- The chosen binary coproduct cofan. -/
noncomputable def cofan (A B : AffinoidAlgebraCat K) : BinaryCofan A B :=
  BinaryCofan.mk (inl K A B) (inr K A B)

/-- The completed tensor product cofan satisfies the binary coproduct universal property. -/
noncomputable def cofanIsColimit (A B : AffinoidAlgebraCat K) :
    IsColimit (cofan K A B) :=
  BinaryCofan.IsColimit.mk _
    (fun {C} f g ↦ AffinoidPresentation.completedTensorLift K
      A.isAffinoid.presentation B.isAffinoid.presentation C.isAffinoid.presentation f g)
    (fun {C} f g ↦ AffinoidPresentation.completedTensorLift_comp_includeLeft K
      A.isAffinoid.presentation B.isAffinoid.presentation C.isAffinoid.presentation f g)
    (fun {C} f g ↦ AffinoidPresentation.completedTensorLift_comp_includeRight K
      A.isAffinoid.presentation B.isAffinoid.presentation C.isAffinoid.presentation f g)
    (fun {C} f g m hleft hright ↦ by
      dsimp [cofan] at m hleft hright
      change AffinoidPresentation.CompletedTensorProduct K
        A.isAffinoid.presentation B.isAffinoid.presentation →ₐ[K] C at m
      change m.comp (AffinoidPresentation.includeLeft K
        A.isAffinoid.presentation B.isAffinoid.presentation) = f at hleft
      change m.comp (AffinoidPresentation.includeRight K
        A.isAffinoid.presentation B.isAffinoid.presentation) = g at hright
      apply AffinoidPresentation.completedTensorProduct_algHom_ext K
        A.isAffinoid.presentation B.isAffinoid.presentation C.isAffinoid.presentation
      · rw [hleft,
          AffinoidPresentation.completedTensorLift_comp_includeLeft K
            A.isAffinoid.presentation B.isAffinoid.presentation C.isAffinoid.presentation f g]
      · rw [hright,
          AffinoidPresentation.completedTensorLift_comp_includeRight K
            A.isAffinoid.presentation B.isAffinoid.presentation C.isAffinoid.presentation f g])

end Coproduct

noncomputable instance hasColimitPair (A B : AffinoidAlgebraCat K) :
    HasColimit (pair A B) :=
  HasColimit.mk
    { cocone := Coproduct.cofan K A B
      isColimit := Coproduct.cofanIsColimit K A B }

noncomputable instance hasBinaryCoproducts : HasBinaryCoproducts (AffinoidAlgebraCat K) :=
  hasBinaryCoproducts_of_hasColimit_pair _

/-- Affinoid spectra, modeled contravariantly by strict affinoid algebras, have binary products. -/
noncomputable instance oppositeHasBinaryProducts :
    HasBinaryProducts (AffinoidAlgebraCat K)ᵒᵖ :=
  inferInstance

end AffinoidAlgebraCat

end Rigid
