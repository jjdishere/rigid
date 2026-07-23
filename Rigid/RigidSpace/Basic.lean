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

namespace AdmissibleLocallyRingedSpace

/-- The admissible opens of `X` contained in `U`. These are the opens of the restricted
admissible site. -/
def OpenBelow (X : AdmissibleLocallyRingedSpace K) (U : X.admissibleTopology.Open) :=
  { V : X.admissibleTopology.Open // V ≤ U }

namespace OpenBelow

instance (X : AdmissibleLocallyRingedSpace K) (U : X.admissibleTopology.Open) :
    PartialOrder (OpenBelow K X U) :=
  inferInstanceAs (PartialOrder { V : X.admissibleTopology.Open // V ≤ U })

/-- The full open of the restricted admissible site. -/
def top (X : AdmissibleLocallyRingedSpace K) (U : X.admissibleTopology.Open) :
    OpenBelow K X U :=
  ⟨U, le_rfl⟩

end OpenBelow

/-- An isomorphism from the restriction of `X` to `U` onto an admissible locally ringed space.

Unlike a comparison of point sets and global sections, this records the full admissible site and
the structure sheaf: admissible opens and covers correspond, and the section isomorphisms commute
with every restriction map. -/
structure RestrictionIso (X Y : AdmissibleLocallyRingedSpace K)
    (U : X.admissibleTopology.Open) where
  /-- Equivalence on analytic points. -/
  pointsEquiv : ↥(U : Set X.points) ≃ Y.points
  /-- Equivalence between admissible opens in the restriction and admissible opens of the model. -/
  openEquiv : OpenBelow K X U ≃ Y.admissibleTopology.Open
  /-- The equivalence on opens preserves and reflects inclusion. -/
  openEquiv_le_iff : ∀ V W, openEquiv V ≤ openEquiv W ↔ V ≤ W
  /-- The equivalences on points and opens preserve membership. -/
  mem_openEquiv : ∀ (x : ↥(U : Set X.points)) (V : OpenBelow K X U),
    pointsEquiv x ∈ (openEquiv V : Set Y.points) ↔ x.1 ∈ (V.1 : Set X.points)
  /-- Admissible covering families correspond. -/
  isCover_iff : ∀ {I : Type (u + 1)} (V : I → OpenBelow K X U) (W : OpenBelow K X U),
    AdmissibleTopology.Open.IsCover X.admissibleTopology (fun i ↦ (V i).1) W.1 ↔
      AdmissibleTopology.Open.IsCover Y.admissibleTopology (fun i ↦ openEquiv (V i))
        (openEquiv W)
  /-- Equivalence on analytic sections over every admissible open. -/
  sectionsEquiv : ∀ V : OpenBelow K X U,
    X.structurePresheaf.Sections V.1 ≃ₐ[K]
      Y.structurePresheaf.Sections (openEquiv V)
  /-- The equivalences on sections commute with restriction. -/
  sectionsEquiv_restriction : ∀ {V W : OpenBelow K X U} (hVW : V ≤ W),
    (sectionsEquiv V).toAlgHom.comp
        (X.structurePresheaf.restriction
          (show (V.1 : Set X.points) ⊆ (W.1 : Set X.points) from fun _ hx ↦ hVW hx)) =
      (Y.structurePresheaf.restriction ((openEquiv_le_iff V W).2 hVW)).comp
        (sectionsEquiv W).toAlgHom

end AdmissibleLocallyRingedSpace

/-- A fully bundled affinoid-spectrum model. Its admissible topology and structure sheaf are part
of the model; they are not reconstructed from an equivalence of point sets and global sections. -/
structure AffinoidSpectrumModel where
  /-- The coordinate algebra. -/
  A : Type u
  [commRing : CommRing A]
  [algebra : Algebra K A]
  /-- The coordinate algebra is strictly affinoid over `K`. -/
  isAffinoid : IsAffinoidAlgebra K A
  /-- The complete admissible locally ringed space underlying the affinoid spectrum. -/
  toAdmissibleLocallyRingedSpace : AdmissibleLocallyRingedSpace K
  /-- The analytic points are the maximal ideals of the coordinate algebra. -/
  pointsEquiv : toAdmissibleLocallyRingedSpace.points ≃ MaximalSpectrum A
  /-- Global analytic functions recover the coordinate algebra. -/
  sectionsEquiv :
    toAdmissibleLocallyRingedSpace.structurePresheaf.Sections
        (AdmissibleTopology.Open.top toAdmissibleLocallyRingedSpace.admissibleTopology) ≃ₐ[K] A

attribute [instance] AffinoidSpectrumModel.commRing AffinoidSpectrumModel.algebra

/-- An affinoid chart around a point of an admissible locally ringed space. The restriction to the
chart domain is identified with a fully bundled affinoid-spectrum model, including its admissible
site and structure sheaf. -/
structure AffinoidChart (X : AdmissibleLocallyRingedSpace K) (x : X.points) where
  /-- The admissible neighborhood underlying the chart. -/
  domain : X.admissibleTopology.Open
  /-- The center belongs to the chart. -/
  mem : x ∈ (domain : Set X.points)
  /-- The affinoid-spectrum model for the chart. -/
  model : AffinoidSpectrumModel K
  /-- Identification of the restricted locally ringed space with the full affinoid model. -/
  restrictionIso :
    AdmissibleLocallyRingedSpace.RestrictionIso K X model.toAdmissibleLocallyRingedSpace domain

/-- A rigid analytic space over `K` is an admissible locally ringed space admitting an affinoid
chart modeled on `MaximalSpectrum A` around every point. -/
structure RigidSpace extends AdmissibleLocallyRingedSpace K where
  /-- Every point has an affinoid neighborhood modeled on `MaximalSpectrum A`. -/
  locallyAffinoid : ∀ x, Nonempty (AffinoidChart K toAdmissibleLocallyRingedSpace x)

namespace RigidSpace

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- A morphism of admissible locally ringed spaces. -/
structure Hom (X Y : RigidSpace K) : Type (u + 1) where
  /-- The map on analytic points. -/
  base : X.points → Y.points
  /-- Inverse image of each admissible open. -/
  preimage : Y.admissibleTopology.Open → X.admissibleTopology.Open
  /-- Membership in an inverse image is detected on points. -/
  mem_preimage : ∀ x U, x ∈ preimage U ↔ base x ∈ U
  /-- Inverse image preserves inclusions of admissible opens. -/
  preimage_mono : ∀ {U V : Y.admissibleTopology.Open}, (U : Set Y.points) ⊆ V →
    (preimage U : Set X.points) ⊆ preimage V
  /-- Pullback of analytic sections. -/
  pullback : ∀ (U : Y.admissibleTopology.Open), Y.structurePresheaf.Sections U →ₐ[K]
    X.structurePresheaf.Sections (preimage U)
  /-- Pullback commutes with restriction. -/
  pullback_restriction : ∀ {U V : Y.admissibleTopology.Open}
      (hUV : (U : Set Y.points) ⊆ V),
    (X.structurePresheaf.restriction (preimage_mono hUV)).comp (pullback V) =
      (pullback U).comp (Y.structurePresheaf.restriction hUV)
  /-- The induced map on local rings. -/
  stalkMap : ∀ x, Y.structurePresheaf.Stalk (base x) →ₐ[K]
    X.structurePresheaf.Stalk x
  /-- Maps on stalks are local homomorphisms. -/
  stalkMap_isLocal : ∀ x, IsLocalHom (stalkMap x)
  /-- Pullback commutes with passage to germs. -/
  pullback_germ : ∀ (x) (U : Y.admissibleTopology.Open)
      (hx : base x ∈ (U : Set Y.points))
      (s : Y.structurePresheaf.Sections U),
    stalkMap x (Y.structurePresheaf.germ hx s) =
      X.structurePresheaf.germ ((mem_preimage x U).2 hx) (pullback U s)

@[ext (iff := false)]
theorem Hom.ext {X Y : RigidSpace K} {f g : Hom K X Y}
    (hbase : f.base = g.base) (hpreimage : f.preimage = g.preimage)
    (hpullback : HEq f.pullback g.pullback) (hstalkMap : HEq f.stalkMap g.stalkMap) : f = g := by
  cases f
  cases g
  cases hbase
  cases hpreimage
  cases hpullback
  cases hstalkMap
  rfl

namespace Hom

variable {X Y Z : RigidSpace K}

/-- Identity morphism of admissible locally ringed spaces. -/
noncomputable def id (X : RigidSpace K) : Hom K X X where
  base := _root_.id
  preimage := _root_.id
  mem_preimage := by intro x U; rfl
  preimage_mono := by intro U V h; exact h
  pullback := fun U ↦ AlgHom.id K _
  pullback_restriction := by
    intro U V hUV
    ext s
    rfl
  stalkMap := fun x ↦ AlgHom.id K _
  stalkMap_isLocal := by
    intro x
    exact ⟨fun a h ↦ h⟩
  pullback_germ := by
    intro x U hx s
    rfl

/-- Composition of morphisms of admissible locally ringed spaces. -/
noncomputable def comp (f : Hom K X Y) (g : Hom K Y Z) : Hom K X Z where
  base := fun x ↦ g.base (f.base x)
  preimage := fun U ↦ f.preimage (g.preimage U)
  mem_preimage := by
    intro x U
    rw [f.mem_preimage, g.mem_preimage]
  preimage_mono := by
    intro U V hUV x hx
    exact (f.mem_preimage x (g.preimage V)).2
      ((g.mem_preimage (f.base x) V).2
        (hUV ((g.mem_preimage (f.base x) U).1
          ((f.mem_preimage x (g.preimage U)).1 hx))))
  pullback := fun U ↦ (f.pullback (g.preimage U)).comp (g.pullback U)
  pullback_restriction := by
    intro U V hUV
    let hUV' : U ≤ V := hUV
    let hg : g.preimage U ≤ g.preimage V := g.preimage_mono hUV'
    let hf := f.preimage_mono hg
    rw [← AlgHom.comp_assoc]
    rw [f.pullback_restriction hg]
    change (f.pullback (g.preimage U)).comp
      ((Y.structurePresheaf.restriction hg).comp (g.pullback V)) =
        (f.pullback (g.preimage U)).comp
          ((g.pullback U).comp (Z.structurePresheaf.restriction hUV'))
    rw [g.pullback_restriction hUV']
  stalkMap := fun x ↦ (f.stalkMap x).comp (g.stalkMap (f.base x))
  stalkMap_isLocal := by
    intro x
    exact ⟨fun a h ↦ (g.stalkMap_isLocal (f.base x)).map_nonunit a
      ((f.stalkMap_isLocal x).map_nonunit (g.stalkMap (f.base x) a) h)⟩
  pullback_germ := by
    intro x U hx s
    change f.stalkMap x (g.stalkMap (f.base x) (Z.structurePresheaf.germ hx s)) = _
    rw [g.pullback_germ (f.base x) U hx s]
    exact f.pullback_germ x (g.preimage U)
      ((g.mem_preimage (f.base x) U).2 hx) (g.pullback U s)

end Hom

noncomputable instance category : Category.{u + 1} (RigidSpace K) where
  Hom := Hom K
  id := Hom.id K
  comp := Hom.comp K
  id_comp f := by
    apply Hom.ext
    · funext x; rfl
    · funext U; rfl
    · apply heq_of_eq
      funext U
      ext s
      rfl
    · apply heq_of_eq
      funext x
      ext s
      rfl
  comp_id f := by
    apply Hom.ext
    · funext x; rfl
    · funext U; rfl
    · apply heq_of_eq
      funext U
      ext s
      rfl
    · apply heq_of_eq
      funext x
      ext s
      rfl
  assoc f g h := by
    apply Hom.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext U
      apply AlgHom.ext
      intro s
      rfl
    · apply heq_of_eq
      funext x
      apply AlgHom.ext
      intro s
      rfl

/-- The type of analytic points, lifted to the public universe of the global-space interface. -/
abbrev Point (X : RigidSpace K) : Type (u + 1) := ULift.{u + 1, u} X.points

namespace Point

/-- The map on analytic points induced by a rigid-space morphism. -/
def map {X Y : RigidSpace K} (f : X ⟶ Y) : Point K X → Point K Y :=
  fun x ↦ ⟨f.base x.down⟩

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
