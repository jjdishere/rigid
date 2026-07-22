import Rigid.RigidSpace.AdmissibleTopology

set_option linter.style.header false

/-!
# Structure sheaves on Tate admissible spaces

The structure presheaf of a rigid space is a presheaf of commutative algebras on the opposite
category of admissible opens. The sheaf axiom is imposed only for the specified admissible covers.
Stalks are the categorical colimits over admissible neighbourhoods, and local ringedness is the
usual local-ring condition on those colimits.
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K]
variable {X : Type u} (T : AdmissibleTopology X)

/-- A presheaf of commutative `K`-algebras on a Tate admissible space. -/
structure AdmissiblePresheaf where
  presheaf : Functor T.Openᵒᵖ (CommAlgCat.{u} K)

namespace AdmissiblePresheaf

variable {K T}

/-- Sections of an admissible presheaf on an admissible open. -/
abbrev Sections (P : AdmissiblePresheaf K T) (U : T.Open) : Type u :=
  P.presheaf.obj (Opposite.op U)

instance sectionsCommRing (P : AdmissiblePresheaf K T) (U : T.Open) :
    CommRing (P.Sections U) :=
  inferInstance

instance sectionsAlgebra (P : AdmissiblePresheaf K T) (U : T.Open) :
    Algebra K (P.Sections U) :=
  inferInstance

/-- Restriction of sections along an inclusion of admissible opens. -/
def restriction (P : AdmissiblePresheaf K T) {U V : T.Open} (hUV : U ≤ V) :
    P.Sections V →ₐ[K] P.Sections U :=
  (P.presheaf.map (homOfLE hUV).op).hom

@[simp]
theorem restriction_id (P : AdmissiblePresheaf K T) (U : T.Open) :
    P.restriction (U := U) (V := U) le_rfl = AlgHom.id K (P.Sections U) := by
  change (P.presheaf.map (homOfLE le_rfl).op).hom = _
  rw [show (homOfLE le_rfl).op = 𝟙 (Opposite.op U) from Subsingleton.elim _ _,
    P.presheaf.map_id]
  rfl

@[simp]
theorem restriction_comp (P : AdmissiblePresheaf K T) {U V W : T.Open}
    (hUV : U ≤ V) (hWU : W ≤ U) :
    (P.restriction hWU).comp (P.restriction hUV) = P.restriction (hWU.trans hUV) := by
  change ((P.presheaf.map (homOfLE hWU).op).hom).comp
      (P.presheaf.map (homOfLE hUV).op).hom =
    (P.presheaf.map (homOfLE (hWU.trans hUV)).op).hom
  rw [← CommAlgCat.hom_comp, ← P.presheaf.map_comp]
  rfl

private theorem inter_le_left (U V : T.Open) :
    AdmissibleTopology.Open.inter T U V ≤ U :=
  Set.inter_subset_left

/-- A family of local sections is compatible when the two restrictions to every pairwise
intersection agree. -/
def IsCompatible (P : AdmissiblePresheaf K T) {I : Type v}
    (U : I → T.Open) (s : ∀ i, P.Sections (U i)) : Prop :=
  ∀ i j,
    P.restriction (inter_le_left (U i) (U j)) (s i) =
      P.restriction (show AdmissibleTopology.Open.inter T (U i) (U j) ≤ U j by
        exact Set.inter_subset_right) (s j)

/-- The sheaf condition for all admissible covering families. -/
def IsSheaf (P : AdmissiblePresheaf K T) : Prop :=
  ∀ {I : Type (u + 1)} {U : I → T.Open} {V : T.Open},
    ∀ hU : AdmissibleTopology.Open.IsCover T U V,
      ∀ (s : ∀ i, P.Sections (U i)), P.IsCompatible U s →
        ∃! t : P.Sections V,
          ∀ i, P.restriction (AdmissibleTopology.Open.IsCover.subset hU i) t = s i

/-- The admissible neighbourhoods of a point, ordered by inclusion. -/
def OpenNeighborhood (x : X) := { U : T.Open // x ∈ (U : Set X) }

namespace OpenNeighborhood

instance (x : X) : PartialOrder (OpenNeighborhood (T := T) x) :=
  inferInstanceAs (PartialOrder { U : T.Open // x ∈ (U : Set X) })

/-- Forget that an admissible open contains the specified point. -/
def inclusion (x : X) : Functor (OpenNeighborhood (T := T) x) T.Open :=
  (Subtype.mono_coe _).functor

end OpenNeighborhood

/-- The directed diagram of section algebras over admissible neighbourhoods of a point. -/
def stalkDiagram (P : AdmissiblePresheaf K T) (x : X) :
    Functor (OpenNeighborhood (T := T) x)ᵒᵖ (CommAlgCat.{u} K) :=
  (OpenNeighborhood.inclusion (T := T) x).op ⋙ P.presheaf

/-- The stalk is the colimit of sections over admissible neighbourhoods. -/
noncomputable abbrev Stalk (P : AdmissiblePresheaf K T) (x : X) : Type u :=
  ↥(colimit (P.stalkDiagram x))

noncomputable instance stalkCommRing (P : AdmissiblePresheaf K T) (x : X) :
    CommRing (P.Stalk x) :=
  inferInstance

noncomputable instance stalkAlgebra (P : AdmissiblePresheaf K T) (x : X) :
    Algebra K (P.Stalk x) :=
  inferInstance

/-- The germ homomorphism from sections on a neighbourhood to the stalk. -/
noncomputable def germ (P : AdmissiblePresheaf K T) {U : T.Open} {x : X}
    (hx : x ∈ (U : Set X)) : P.Sections U →ₐ[K] P.Stalk x :=
  (colimit.ι (P.stalkDiagram x) (Opposite.op ⟨U, hx⟩)).hom

/-- A structure presheaf is locally ringed when every categorical stalk is a local ring. -/
def IsLocallyRinged (P : AdmissiblePresheaf K T) : Prop :=
  ∀ x, IsLocalRing (P.Stalk x)

/-- A structure sheaf on a Tate admissible space is a sheaf of commutative `K`-algebras with local
stalks. -/
structure IsStructureSheaf (P : AdmissiblePresheaf K T) : Prop where
  isSheaf : P.IsSheaf
  isLocallyRinged : P.IsLocallyRinged

end AdmissiblePresheaf

end Rigid
