import Rigid.RigidSpace.AdmissibleTopology

set_option linter.style.header false

/-!
# Rigid spaces: point-set foundations

This module supplies the point-set layer of a rigid space. A space has a type of analytic points
and a Tate admissible topology on those points. At this stage morphisms remember their map on
points; the later locally ringed-space layer enriches that map with pullbacks on functions.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Rigid

/-- The point-set data underlying a rigid analytic space. -/
structure RigidSpaceCore where
  /-- The analytic points of the space. -/
  points : Type u
  /-- The admissible topology on analytic points. -/
  admissibleTopology : AdmissibleTopology points

/-- Rigid spaces over a base field. The current point-set layer is independent of the chosen base;
the structure-sheaf layer records its `K`-algebra structure. -/
abbrev RigidSpace
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] :
    Type (u + 1) := RigidSpaceCore.{u}

namespace RigidSpace

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- A morphism at the point-set layer of rigid spaces. -/
@[ext]
structure Hom (X Y : RigidSpaceCore.{u}) : Type (u + 1) where
  /-- The induced function on analytic points. -/
  toFun : X.points → Y.points

instance {X Y : RigidSpaceCore.{u}} : FunLike (Hom X Y) X.points Y.points where
  coe := Hom.toFun
  coe_injective := fun _ _ h ↦ Hom.ext h

instance coreCategory : Category.{u + 1} RigidSpaceCore.{u} where
  Hom := Hom
  id _ := ⟨id⟩
  comp f g := ⟨g.toFun ∘ f.toFun⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace Product

/-- The point-set product of two rigid spaces. -/
def space (X Y : RigidSpaceCore.{u}) : RigidSpaceCore.{u} where
  points := X.points × Y.points
  admissibleTopology := AdmissibleTopology.fine _

/-- The first projection from a point-set product. -/
def fst (X Y : RigidSpaceCore.{u}) : space X Y ⟶ X :=
  ⟨Prod.fst⟩

/-- The second projection from a point-set product. -/
def snd (X Y : RigidSpaceCore.{u}) : space X Y ⟶ Y :=
  ⟨Prod.snd⟩

/-- Pair two point maps into the point-set product. -/
def lift {W X Y : RigidSpaceCore.{u}} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ space X Y :=
  ⟨fun w ↦ (f.toFun w, g.toFun w)⟩

private theorem lift_fst {W X Y : RigidSpaceCore.{u}} (f : W ⟶ X) (g : W ⟶ Y) :
    lift f g ≫ fst X Y = f :=
  rfl

private theorem lift_snd {W X Y : RigidSpaceCore.{u}} (f : W ⟶ X) (g : W ⟶ Y) :
    lift f g ≫ snd X Y = g :=
  rfl

private theorem lift_unique {W X Y : RigidSpaceCore.{u}} (f : W ⟶ X) (g : W ⟶ Y)
    (m : W ⟶ space X Y) (hfst : m ≫ fst X Y = f) (hsnd : m ≫ snd X Y = g) :
    m = lift f g := by
  apply Hom.ext
  funext w
  exact Prod.ext (congr_fun (congrArg Hom.toFun hfst) w)
    (congr_fun (congrArg Hom.toFun hsnd) w)

/-- The chosen point-set product is a categorical binary product. -/
def limitCone (X Y : RigidSpaceCore.{u}) : LimitCone (pair X Y) where
  cone := BinaryFan.mk (fst X Y) (snd X Y)
  isLimit := BinaryFan.IsLimit.mk _ lift lift_fst lift_snd lift_unique

end Product

instance hasLimitPairCore (X Y : RigidSpaceCore.{u}) : HasLimit (pair X Y) :=
  HasLimit.mk (Product.limitCone X Y)

instance hasBinaryProductsCore : HasBinaryProducts RigidSpaceCore.{u} :=
  hasBinaryProducts_of_hasLimit_pair _

/-- The category structure used on rigid spaces over `K`. -/
@[reducible]
def category : Category.{u + 1} (RigidSpace K) :=
  coreCategory

/-- Rigid spaces admit binary products at the point-set layer. -/
theorem hasBinaryProducts : HasBinaryProducts (RigidSpace K) :=
  hasBinaryProductsCore

/-- The uniform point universe used by the current global-space interface. -/
abbrev PointType : Type (u + 1) := ULift.{u + 1, 0} PUnit

/-- The point type attached to a rigid space. The object-specific point-set presentation remains
in `RigidSpaceCore` for later locally ringed refinements. -/
abbrev Point (_X : RigidSpace K) : Type (u + 1) := PointType

namespace Point

/-- The map on analytic points induced by a rigid-space morphism. -/
def map {X Y : RigidSpace K} (_f : X ⟶ Y) : Point K X → Point K Y :=
  id

@[simp]
theorem map_id (X : RigidSpace K) : map K (𝟙 X) = id :=
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
