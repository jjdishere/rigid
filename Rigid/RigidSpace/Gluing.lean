import Rigid.RigidSpace.Basic

set_option linter.style.header false

/-!
# Quotient/site transport and effective gluing

This module contains two complementary gluing constructions. `ChartGluingData` forms the actual
quotient of a disjoint union of independent chart point sets, equips it with the chart-induced
admissible topology, and builds its structure presheaf from compatible families of chart sections.
Effective sheaf, local-stalk, and locally-affinoid descent promote that object to an admissible
locally ringed space or a rigid space. `SiteTransport` and `QuotientGluingData` verify reconstruction
of an already-glued space from an admissible cover.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

namespace AdmissibleLocallyRingedSpace

/-- Site data identifying a quotient point set with an existing admissible locally ringed space. -/
structure SiteTransport (X : AdmissibleLocallyRingedSpace K)
    (Q : Type u) (TQ : AdmissibleTopology Q) where
  /-- Equivalence between quotient points and points of the original space. -/
  pointsEquiv : Q ≃ X.points
  /-- Equivalence between admissible opens. -/
  openEquiv : TQ.Open ≃ X.admissibleTopology.Open
  /-- The open equivalence preserves and reflects inclusions. -/
  openEquiv_le_iff : ∀ U V, openEquiv U ≤ openEquiv V ↔ U ≤ V
  /-- The open equivalence preserves admissible covers. -/
  isCover_iff : ∀ {I : Type (u + 1)} (U : I → TQ.Open) (V : TQ.Open),
    AdmissibleTopology.Open.IsCover TQ U V ↔
      AdmissibleTopology.Open.IsCover X.admissibleTopology
        (fun i ↦ openEquiv (U i)) (openEquiv V)
  /-- The open equivalence preserves binary intersections. -/
  openEquiv_inter : ∀ U V,
    openEquiv (AdmissibleTopology.Open.inter TQ U V) =
      AdmissibleTopology.Open.inter X.admissibleTopology (openEquiv U) (openEquiv V)
  /-- Compatibility on quotient intersections transports to compatibility on the original site. -/
  compatible_of : ∀ {I : Type (u + 1)} (U : I → TQ.Open)
      (s : ∀ i, X.structurePresheaf.Sections (openEquiv (U i))),
    (∀ i j,
      X.structurePresheaf.restriction
          ((openEquiv_le_iff _ _).2
            (show AdmissibleTopology.Open.inter TQ (U i) (U j) ≤ U i from
              Set.inter_subset_left)) (s i) =
        X.structurePresheaf.restriction
          ((openEquiv_le_iff _ _).2
            (show AdmissibleTopology.Open.inter TQ (U i) (U j) ≤ U j from
              Set.inter_subset_right)) (s j)) →
      X.structurePresheaf.IsCompatible (fun i ↦ openEquiv (U i)) s
  /-- Point membership is preserved by the site equivalence. -/
  mem_openEquiv : ∀ (q : Q) (U : TQ.Open),
    pointsEquiv q ∈ (openEquiv U : Set X.points) ↔ q ∈ (U : Set Q)

namespace SiteTransport

/-- The functor on opposite open categories induced by the site equivalence. -/
def openFunctor {X : AdmissibleLocallyRingedSpace K}
    {Q : Type u} {TQ : AdmissibleTopology Q} (D : SiteTransport K X Q TQ) :
    TQ.Openᵒᵖ ⥤ X.admissibleTopology.Openᵒᵖ where
  obj U := Opposite.op (D.openEquiv (Opposite.unop U))
  map {U V} f := by
    let h : D.openEquiv (Opposite.unop V) ≤ D.openEquiv (Opposite.unop U) := by
      apply (D.openEquiv_le_iff _ _).2
      exact leOfHom f.unop
    exact (homOfLE h).op
  map_id := by
    intro U
    apply Subsingleton.elim
  map_comp := by
    intro U V W f g
    apply Subsingleton.elim

/-- The presheaf transported along a quotient/site presentation. -/
def transportedPresheaf {X : AdmissibleLocallyRingedSpace K}
    {Q : Type u} {TQ : AdmissibleTopology Q} (D : SiteTransport K X Q TQ) :
    AdmissiblePresheaf K TQ where
  presheaf := D.openFunctor ⋙ X.structurePresheaf.presheaf

@[simp]
theorem transportedPresheaf_sections {X : AdmissibleLocallyRingedSpace K}
    {Q : Type u} {TQ : AdmissibleTopology Q} (D : SiteTransport K X Q TQ)
    (U : TQ.Open) :
    (D.transportedPresheaf).Sections U =
      X.structurePresheaf.Sections (D.openEquiv U) :=
  rfl

@[simp]
theorem transportedPresheaf_restriction {X : AdmissibleLocallyRingedSpace K}
    {Q : Type u} {TQ : AdmissibleTopology Q} (D : SiteTransport K X Q TQ)
    {U V : TQ.Open} (hUV : U ≤ V) :
    (D.transportedPresheaf).restriction hUV =
      X.structurePresheaf.restriction ((D.openEquiv_le_iff U V).2 hUV) := by
  rfl

/-- A stalk-locality certificate for the transported presheaf. -/
structure StalkLocality {X : AdmissibleLocallyRingedSpace K}
    {Q : Type u} {TQ : AdmissibleTopology Q} (D : SiteTransport K X Q TQ) : Prop where
  isLocal : ∀ q, IsLocalRing (D.transportedPresheaf.Stalk q)

private theorem transported_isCompatible {X : AdmissibleLocallyRingedSpace K}
    {Q : Type u} {TQ : AdmissibleTopology Q} (D : SiteTransport K X Q TQ)
    {I : Type (u + 1)} {U : I → TQ.Open}
    {s : ∀ i, D.transportedPresheaf.Sections (U i)}
    (hs : D.transportedPresheaf.IsCompatible U s) :
    X.structurePresheaf.IsCompatible (fun i ↦ D.openEquiv (U i)) s := by
  apply D.compatible_of U s
  intro i j
  exact hs i j

/-- The transported presheaf is a sheaf whenever the original presheaf is a sheaf. -/
theorem transported_isSheaf {X : AdmissibleLocallyRingedSpace K}
    {Q : Type u} {TQ : AdmissibleTopology Q} (D : SiteTransport K X Q TQ) :
    D.transportedPresheaf.IsSheaf := by
  intro I U V hU s hs
  have hU' := (D.isCover_iff U V).mp hU
  have hs' := transported_isCompatible (K := K) D hs
  obtain ⟨t, ht, htu⟩ := X.isStructureSheaf.isSheaf hU' s hs'
  refine ⟨t, ?_, ?_⟩
  · intro i
    change X.structurePresheaf.restriction _ t = s i
    exact ht i
  · intro t' ht'
    apply htu (t' : X.structurePresheaf.Sections (D.openEquiv V))
    intro i
    have hi := ht' i
    change X.structurePresheaf.restriction _ t' = s i at hi
    exact hi

/-- The locally ringed space obtained by transporting the quotient/site data. -/
noncomputable def transported (X : AdmissibleLocallyRingedSpace K)
    {Q : Type u} {TQ : AdmissibleTopology Q} (D : SiteTransport K X Q TQ)
    (hlocal : D.StalkLocality) : AdmissibleLocallyRingedSpace K where
  points := Q
  admissibleTopology := TQ
  structurePresheaf := D.transportedPresheaf
  isStructureSheaf :=
    { isSheaf := transported_isSheaf (K := K) D
      isLocallyRinged := hlocal.isLocal }

end SiteTransport

/-- A family of admissible locally ringed spaces together with the equivalence relation used to
identify their points. This is the point-level input for gluing independent charts. -/
structure ChartGluingData where
  /-- The chart indices. -/
  index : Type u
  /-- The locally ringed chart at each index. -/
  chart : index → AdmissibleLocallyRingedSpace K
  /-- The overlap equivalence relation on the disjoint union of chart points. -/
  relation : Setoid (Σ i, (chart i).points)

namespace ChartGluingData

/-- The disjoint union of all chart point sets. -/
abbrev totalPoints (G : ChartGluingData K) :=
  Σ i, (G.chart i).points

/-- The point set obtained by identifying chart points on overlaps. -/
abbrev quotientPoints (G : ChartGluingData K) :=
  Quotient G.relation

/-- The canonical map from a chart to the quotient point set. -/
def chartMap (G : ChartGluingData K) (i : G.index) :
    (G.chart i).points → G.quotientPoints :=
  fun x ↦ Quotient.mk G.relation ⟨i, x⟩

/-- The inverse image in a chart of a subset of the quotient. -/
def chartPreimage (G : ChartGluingData K) (i : G.index)
    (U : Set G.quotientPoints) : Set (G.chart i).points :=
  (chartMap K G i) ⁻¹' U

/-- Two chart points have the same image in the quotient precisely when the gluing relation
identifies them. -/
theorem chartMap_eq_iff (G : ChartGluingData K) {i j : G.index}
    {x : (G.chart i).points} {y : (G.chart j).points} :
    chartMap K G i x = chartMap K G j y ↔ G.relation.r ⟨i, x⟩ ⟨j, y⟩ :=
  Quotient.eq

/-- Every quotient point comes from one of the charts. -/
theorem chartMap_jointly_surjective (G : ChartGluingData K) (q : G.quotientPoints) :
    ∃ i, ∃ x : (G.chart i).points, chartMap K G i x = q := by
  obtain ⟨z, rfl⟩ := Quotient.exists_rep q
  exact ⟨z.1, z.2, rfl⟩

/-- The quotient admissible topology. Opens and covering families are detected after inverse image
in every chart. -/
def quotientTopology (G : ChartGluingData K) : AdmissibleTopology G.quotientPoints where
  IsOpen U := ∀ i, (G.chart i).admissibleTopology.IsOpen (chartPreimage K G i U)
  isOpen_univ := by
    intro i
    change (G.chart i).admissibleTopology.IsOpen Set.univ
    exact (G.chart i).admissibleTopology.isOpen_univ
  isOpen_inter := by
    intro U V hU hV i
    change (G.chart i).admissibleTopology.IsOpen
      (chartPreimage K G i U ∩ chartPreimage K G i V)
    exact (G.chart i).admissibleTopology.isOpen_inter (hU i) (hV i)
  Covers := fun family U ↦ ∀ i,
    (G.chart i).admissibleTopology.Covers
      (chartPreimage K G i '' family) (chartPreimage K G i U)
  covers_isOpen := by
    intro U family h
    refine ⟨fun i ↦ ((G.chart i).admissibleTopology.covers_isOpen (h i)).1, ?_⟩
    intro V hV i
    exact ((G.chart i).admissibleTopology.covers_isOpen (h i)).2
      (chartPreimage K G i V) ⟨V, hV, rfl⟩
  covers_subset := by
    intro U family h V hV q hq
    refine Quotient.inductionOn q ?_ hq
    intro z hz
    exact (G.chart z.1).admissibleTopology.covers_subset (h z.1)
      (chartPreimage K G z.1 V) ⟨V, hV, rfl⟩ hz
  covers_sUnion := by
    intro U family h
    ext q
    refine Quotient.inductionOn q ?_
    intro z
    have hz := Set.ext_iff.mp
      ((G.chart z.1).admissibleTopology.covers_sUnion (h z.1)) z.2
    simpa [chartPreimage, chartMap] using hz
  singleton := by
    intro U hU i
    convert (G.chart i).admissibleTopology.singleton (hU i) using 1 <;>
      ext V <;> simp
  pullback := by
    intro U W family hU hW i
    convert (G.chart i).admissibleTopology.pullback (hU i) (hW i) using 1 <;>
      ext V <;> simp [chartPreimage, chartMap]
  transitive := by
    intro U family refinement hU hRefinement hOpen i
    apply (G.chart i).admissibleTopology.transitive (hU i)
    · rintro V ⟨W, hW, rfl⟩
      obtain ⟨subcover, hSubcover, hSubcoverRefines⟩ := hRefinement W hW
      exact ⟨chartPreimage K G i '' subcover, hSubcover i,
        Set.image_mono hSubcoverRefines⟩
    · rintro V ⟨W, hW, rfl⟩
      exact ⟨(hOpen W hW).1 i, fun _ hx ↦ (hOpen W hW).2 hx⟩

/-- The pullback of a quotient admissible open to a chart. -/
def chartOpen (G : ChartGluingData K) (U : G.quotientTopology.Open) (i : G.index) :
    (G.chart i).admissibleTopology.Open :=
  ⟨chartPreimage K G i U, U.2 i⟩

theorem chartOpen_mono (G : ChartGluingData K) {U V : G.quotientTopology.Open}
    (hUV : U ≤ V) (i : G.index) : chartOpen K G U i ≤ chartOpen K G V i :=
  fun _ hx ↦ hUV hx

/-- Families of chart sections over the inverse images of a quotient open. -/
abbrev LocalSections (G : ChartGluingData K) (U : G.quotientTopology.Open) :=
  ∀ i, (G.chart i).structurePresheaf.Sections (chartOpen K G U i)

/-- Componentwise restriction of a family of chart sections. -/
def localRestriction (G : ChartGluingData K) {U V : G.quotientTopology.Open}
    (hUV : U ≤ V) : LocalSections K G V →ₐ[K] LocalSections K G U where
  toFun s i :=
    (G.chart i).structurePresheaf.restriction (chartOpen_mono K G hUV i) (s i)
  map_one' := by
    funext i
    exact map_one _
  map_mul' s t := by
    funext i
    exact map_mul _ _ _
  map_zero' := by
    funext i
    exact map_zero _
  map_add' s t := by
    funext i
    exact map_add _ _ _
  commutes' c := by
    funext i
    exact ((G.chart i).structurePresheaf.restriction
      (chartOpen_mono K G hUV i)).commutes c

@[simp]
theorem localRestriction_apply (G : ChartGluingData K) {U V : G.quotientTopology.Open}
    (hUV : U ≤ V) (s : LocalSections K G V) (i : G.index) :
    localRestriction K G hUV s i =
      (G.chart i).structurePresheaf.restriction (chartOpen_mono K G hUV i) (s i) :=
  rfl

@[simp]
theorem localRestriction_id (G : ChartGluingData K) (U : G.quotientTopology.Open) :
    localRestriction K G (le_refl U) = AlgHom.id K (LocalSections K G U) := by
  apply AlgHom.ext
  intro s
  funext i
  change (G.chart i).structurePresheaf.restriction _ (s i) = s i
  simpa using congr_fun
    ((G.chart i).structurePresheaf.restriction_id (chartOpen K G U i)) (s i)

@[simp]
theorem localRestriction_comp (G : ChartGluingData K)
    {U V W : G.quotientTopology.Open} (hUV : U ≤ V) (hVW : V ≤ W) :
    (localRestriction K G hUV).comp (localRestriction K G hVW) =
      localRestriction K G (hUV.trans hVW) := by
  apply AlgHom.ext
  intro s
  funext i
  change (G.chart i).structurePresheaf.restriction _
      ((G.chart i).structurePresheaf.restriction _ (s i)) = _
  exact congrArg (fun f ↦ f (s i))
    (AdmissiblePresheaf.restriction_comp (G.chart i).structurePresheaf
      (chartOpen_mono K G hVW i) (chartOpen_mono K G hUV i))

/-- A subalgebra of chartwise sections is the compatible-family part of a quotient open. The
restriction-closure field is the effective descent condition needed to form a presheaf. -/
structure SectionDescent (G : ChartGluingData K) where
  /-- Compatible local sections on each quotient open. -/
  compatibleSections : ∀ U : G.quotientTopology.Open,
    Subalgebra K (LocalSections K G U)
  /-- Restricting a compatible family remains compatible. -/
  restriction_mem : ∀ {U V : G.quotientTopology.Open} (hUV : U ≤ V)
    (s : compatibleSections V),
    localRestriction K G hUV s.1 ∈ compatibleSections U

namespace SectionDescent

/-- Restriction on the compatible-family algebras. -/
def restriction (D : SectionDescent K G) {U V : G.quotientTopology.Open}
    (hUV : U ≤ V) :
    D.compatibleSections V →ₐ[K] D.compatibleSections U :=
  AlgHom.codRestrict
    ((localRestriction K G hUV).comp (D.compatibleSections V).val)
    (D.compatibleSections U)
    (fun s ↦ D.restriction_mem hUV s)

@[simp]
theorem restriction_apply (D : SectionDescent K G)
    {U V : G.quotientTopology.Open} (hUV : U ≤ V)
    (s : D.compatibleSections V) (i : G.index) :
    (restriction K D hUV s).1 i =
      (G.chart i).structurePresheaf.restriction (chartOpen_mono K G hUV i) (s.1 i) :=
  rfl

@[simp]
theorem restriction_id (D : SectionDescent K G) (U : G.quotientTopology.Open) :
    restriction K D (le_refl U) = AlgHom.id K (D.compatibleSections U) := by
  apply AlgHom.ext
  intro s
  apply Subtype.ext
  exact congr_arg (fun f ↦ f s.1) (localRestriction_id K G U)

@[simp]
theorem restriction_comp (D : SectionDescent K G)
    {U V W : G.quotientTopology.Open} (hUV : U ≤ V) (hVW : V ≤ W) :
    (restriction K D hUV).comp (restriction K D hVW) =
      restriction K D (hUV.trans hVW) := by
  apply AlgHom.ext
  intro s
  apply Subtype.ext
  exact congr_arg (fun f ↦ f s.1) (localRestriction_comp K G hUV hVW)

/-- The presheaf of compatible chart sections. -/
def presheaf (D : SectionDescent K G) :
    AdmissiblePresheaf K (quotientTopology K G) where
  presheaf :=
    { obj := fun U ↦ CommAlgCat.of K (D.compatibleSections (Opposite.unop U))
      map := fun f ↦ CommAlgCat.ofHom
        (restriction K D (leOfHom f.unop))
      map_id := by
        intro U
        apply CommAlgCat.hom_ext
        exact restriction_id K D (Opposite.unop U)
      map_comp := by
        intro U V W f g
        apply CommAlgCat.hom_ext
        exact (restriction_comp K D (leOfHom g.unop) (leOfHom f.unop)).symm }

@[simp]
theorem presheaf_sections (D : SectionDescent K G) (U : G.quotientTopology.Open) :
    (presheaf K D).Sections U = D.compatibleSections U :=
  rfl

@[simp]
theorem presheaf_restriction (D : SectionDescent K G)
    {U V : G.quotientTopology.Open} (hUV : U ≤ V) :
    (presheaf K D).restriction hUV = restriction K D hUV :=
  rfl

/-- Effective descent data consists of the compatible-family presheaf together with its sheaf and
local-stalk certificates. -/
structure Effective (D : SectionDescent K G) : Prop where
  isSheaf : (presheaf K D).IsSheaf
  isLocallyRinged : (presheaf K D).IsLocallyRinged

/-- The globally glued locally ringed space. -/
noncomputable def glued (D : SectionDescent K G) (hD : D.Effective) :
    AdmissibleLocallyRingedSpace K where
  points := G.quotientPoints
  admissibleTopology := G.quotientTopology
  structurePresheaf := presheaf K D
  isStructureSheaf :=
    { isSheaf := hD.isSheaf
      isLocallyRinged := hD.isLocallyRinged }

@[simp]
theorem glued_points (D : SectionDescent K G) (hD : D.Effective) :
    (glued K D hD).points = G.quotientPoints :=
  rfl

/-- Effective rigid descent additionally records the inherited affinoid charts on the quotient. -/
structure EffectiveRigid (D : SectionDescent K G) extends D.Effective where
  locallyAffinoid : ∀ q,
    Nonempty (AffinoidChart K (glued K D toEffective) q)

/-- The rigid space obtained by gluing locally affinoid chart data. -/
noncomputable def gluedRigidSpace (D : SectionDescent K G) (hD : D.EffectiveRigid) :
    RigidSpace K where
  toAdmissibleLocallyRingedSpace := glued K D hD.toEffective
  locallyAffinoid := hD.locallyAffinoid

@[simp]
theorem gluedRigidSpace_points (D : SectionDescent K G) (hD : D.EffectiveRigid) :
    (gluedRigidSpace K D hD).points = G.quotientPoints :=
  rfl

end SectionDescent

end ChartGluingData

/-- The disjoint union of the point sets in an admissible cover. -/
structure AdmissibleCover (X : AdmissibleLocallyRingedSpace K) where
  index : Type u
  domain : index → X.admissibleTopology.Open
  isCover : AdmissibleTopology.Open.IsCover X.admissibleTopology domain
    (AdmissibleTopology.Open.top X.admissibleTopology)

namespace AdmissibleCover

theorem exists_mem {X : AdmissibleLocallyRingedSpace K}
    (𝒰 : AdmissibleCover K X) (x : X.points) :
    ∃ i : 𝒰.index, x ∈ (𝒰.domain i : Set X.points) := by
  have h := AdmissibleTopology.Open.IsCover.iUnion 𝒰.isCover
  have hx : x ∈ (AdmissibleTopology.Open.top X.admissibleTopology : Set X.points) := trivial
  rw [h] at hx
  exact Set.mem_iUnion.mp hx

/-- Points in a cover before quotienting overlaps. -/
abbrev totalPoints {X : AdmissibleLocallyRingedSpace K}
    (𝒰 : AdmissibleCover K X) :=
  Σ i, ↥((𝒰.domain i : Set X.points))

/-- The ambient point represented by a point in a cover chart. -/
def ambient {X : AdmissibleLocallyRingedSpace K}
    (𝒰 : AdmissibleCover K X) : 𝒰.totalPoints → X.points :=
  fun z ↦ z.2.1

/-- Equality of ambient points is the overlap relation on the disjoint union. -/
def relation {X : AdmissibleLocallyRingedSpace K}
    (𝒰 : AdmissibleCover K X) : Setoid 𝒰.totalPoints where
  r x y := ambient K 𝒰 x = ambient K 𝒰 y
  iseqv := ⟨
    by intro x; rfl,
    by intro x y h; change ambient K 𝒰 x = ambient K 𝒰 y at h; exact h.symm,
    by intro x y z h₁ h₂; change ambient K 𝒰 x = ambient K 𝒰 y at h₁
     ; change ambient K 𝒰 y = ambient K 𝒰 z at h₂; exact h₁.trans h₂⟩

/-- The quotient point set obtained by identifying equal ambient points. -/
abbrev quotientPoints {X : AdmissibleLocallyRingedSpace K}
    (𝒰 : AdmissibleCover K X) := Quotient 𝒰.relation

/-- The quotient map from cover points to quotient points. -/
def quotientMap {X : AdmissibleLocallyRingedSpace K}
    (𝒰 : AdmissibleCover K X) : 𝒰.totalPoints → 𝒰.quotientPoints :=
  Quotient.mk 𝒰.relation

/-- The quotient is canonically equivalent to the ambient point set. -/
noncomputable def quotientEquiv {X : AdmissibleLocallyRingedSpace K}
    (𝒰 : AdmissibleCover K X) : 𝒰.quotientPoints ≃ X.points where
  toFun := Quotient.lift (ambient K 𝒰) (fun _ _ h ↦ by
    change ambient K 𝒰 _ = ambient K 𝒰 _ at h
    exact h)
  invFun := fun x ↦
    let i := Classical.choose (AdmissibleCover.exists_mem (K := K) 𝒰 x)
    let hi := Classical.choose_spec (AdmissibleCover.exists_mem (K := K) 𝒰 x)
    Quotient.mk 𝒰.relation ⟨i, ⟨x, hi⟩⟩
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    apply Quotient.sound
    rfl
  right_inv := by
    intro x
    change x = x
    rfl

end AdmissibleCover

/-- Complete effective gluing data for a cover. The quotient relation is fixed by the cover; the
admissible site equivalence and stalk-locality certificate are the descent conditions. -/
structure QuotientGluingData (X : AdmissibleLocallyRingedSpace K)
    extends AdmissibleCover K X where
  /-- Admissible topology on the quotient point set. -/
  quotientTopology : AdmissibleTopology (toAdmissibleCover.quotientPoints)
  /-- Identification of the quotient site with the original site. -/
  siteTransport : SiteTransport K X toAdmissibleCover.quotientPoints quotientTopology
  /-- The site point equivalence is the quotient equivalence induced by the cover. -/
  points_quotient : siteTransport.pointsEquiv = toAdmissibleCover.quotientEquiv
  /-- Locality of quotient stalks. -/
  stalkLocality : siteTransport.StalkLocality

namespace QuotientGluingData

/-- The globally glued admissible locally ringed space. -/
noncomputable def glued {X : AdmissibleLocallyRingedSpace K}
    (G : QuotientGluingData K X) : AdmissibleLocallyRingedSpace K :=
  SiteTransport.transported K X G.siteTransport G.stalkLocality

@[simp]
theorem glued_points {X : AdmissibleLocallyRingedSpace K}
    (G : QuotientGluingData K X) : (G.glued K).points = G.toAdmissibleCover.quotientPoints :=
  rfl

/-- The quotient map from each cover chart into the glued point space. -/
def chartPointMap {X : AdmissibleLocallyRingedSpace K}
    (G : QuotientGluingData K X) (i : G.index) :
    ↥((G.domain i : Set X.points)) → (G.glued K).points :=
  G.toAdmissibleCover.quotientMap ∘ fun x ↦ ⟨i, x⟩

theorem chartPointMap_jointly_surjective {X : AdmissibleLocallyRingedSpace K}
    (G : QuotientGluingData K X) (q : (G.glued K).points) :
    ∃ i, ∃ x : ↥((G.domain i : Set X.points)), G.chartPointMap K i x = q := by
  obtain ⟨z, rfl⟩ := Quotient.exists_rep q
  exact ⟨z.1, z.2, rfl⟩

end QuotientGluingData

end AdmissibleLocallyRingedSpace

end Rigid
