import Rigid.AffinoidAlgebra.MaximalSpectrum
import Rigid.RigidSpace.StructureSheaf

set_option linter.style.header false

/-!
# Rigid spaces

This module defines a rigid space as an admissible locally ringed space which is locally modeled on
maximal spectra of strict affinoid algebras.
-/

open CategoryTheory

universe u

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- A locally ringed space for Tate's admissible topology. -/
structure AdmissibleLocallyRingedSpace where
  /-- The analytic points of the space. -/
  points : Type u
  /-- Tate's admissible topology on the analytic points. -/
  admissibleTopology : AdmissibleTopology points
  /-- The presheaf of analytic `K`-algebras. -/
  structurePresheaf : AdmissiblePresheaf K admissibleTopology
  /-- Analytic functions form a sheaf and all stalks are local rings. -/
  isStructureSheaf : structurePresheaf.IsStructureSheaf

/-- An affinoid chart around a point of an admissible locally ringed space. The chart identifies
its points with the maximal spectrum of a strict affinoid algebra and its analytic functions with
that algebra. -/
structure AffinoidChart (X : AdmissibleLocallyRingedSpace K) (x : X.points) where
  /-- The admissible neighborhood underlying the chart. -/
  domain : X.admissibleTopology.Open
  /-- The center belongs to the chart. -/
  mem : x ∈ (domain : Set X.points)
  /-- The coordinate algebra of the chart. -/
  A : Type u
  [commRing : CommRing A]
  [algebra : Algebra K A]
  /-- The coordinate algebra is strictly affinoid over `K`. -/
  isAffinoid : IsAffinoidAlgebra K A
  /-- The chart points are the maximal ideals of its coordinate algebra. -/
  pointsEquiv : ↥(domain : Set X.points) ≃ MaximalSpectrum A
  /-- Analytic functions on the chart recover its coordinate algebra. -/
  sectionsEquiv : X.structurePresheaf.Sections domain ≃ₐ[K] A

attribute [instance] AffinoidChart.commRing AffinoidChart.algebra

/-- A rigid analytic space over `K` is an admissible locally ringed space admitting an affinoid
chart modeled on `MaximalSpectrum A` around every point. -/
structure RigidSpace extends AdmissibleLocallyRingedSpace K where
  /-- Every point has an affinoid neighborhood modeled on `MaximalSpectrum A`. -/
  locallyAffinoid : ∀ x, Nonempty (AffinoidChart K toAdmissibleLocallyRingedSpace x)

namespace RigidSpace

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- A morphism at the point-set layer of rigid spaces. -/
@[ext]
structure Hom (X Y : RigidSpace K) : Type (u + 1) where
  /-- The induced function on analytic points. -/
  toFun : X.points → Y.points

instance {X Y : RigidSpace K} : FunLike (Hom K X Y) X.points Y.points where
  coe := Hom.toFun
  coe_injective := fun _ _ h ↦ Hom.ext h

instance category : Category.{u + 1} (RigidSpace K) where
  Hom := Hom K
  id _ := ⟨id⟩
  comp f g := ⟨g.toFun ∘ f.toFun⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The type of analytic points, lifted to the public universe of the global-space interface. -/
abbrev Point (X : RigidSpace K) : Type (u + 1) := ULift.{u + 1, u} X.points

namespace Point

/-- The map on analytic points induced by a rigid-space morphism. -/
def map {X Y : RigidSpace K} (f : X ⟶ Y) : Point K X → Point K Y :=
  fun x ↦ ⟨f.toFun x.down⟩

@[simp]
theorem map_id (X : RigidSpace K) : map K (𝟙 X) = id :=
  by
    funext x
    cases x
    rfl

@[simp]
theorem map_comp {X Y Z : RigidSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map K (f ≫ g) = map K g ∘ map K f :=
  rfl

end Point

/-- The functor assigning to a rigid space its type of analytic points. -/
def pointFunctor : RigidSpace K ⥤ Type (u + 1) where
  obj X := Point K X
  map f := TypeCat.ofHom (Point.map K f)
  map_id X := by apply TypeCat.homEquiv.injective; exact Point.map_id K X
  map_comp _ _ := rfl

end RigidSpace

end Rigid
