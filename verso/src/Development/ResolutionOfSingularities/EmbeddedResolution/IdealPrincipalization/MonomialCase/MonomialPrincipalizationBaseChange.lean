import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCasePrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialBlowupIteration
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialInvariantDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonotoneInvariantSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

noncomputable abbrev MarkedIdealWithBoundary.pullbackWithBoundary (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (E' : List Y.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  (T.pullbackOverField Y k' q g).withBoundary E'

/- English proof (authored)
The unit ideal has empty support. Membership of the given point in that support is therefore impossible.
-/
private theorem false_of_mem_support_top {X : Scheme.{u}} (y : ↥X)
    (h : y ∈ (⊤ : X.IdealSheafData).support) : False := by
  have hb : (⊤ : X.IdealSheafData).support = ⊥ :=
    (Scheme.IdealSheafData.support_eq_bot_iff _).mpr rfl
  rw [hb] at h
  have h' : y ∈ ((⊥ : TopologicalSpace.Closeds ↥X) : Set ↥X) := h
  rw [TopologicalSpace.Closeds.coe_bot] at h'
  simp at h'

/- English proof (authored)
If the image point is in the support, the given point is in the support of the pulled-back ideal by the inverse-image formula for support. That ideal is the unit ideal and has empty support, a contradiction.
-/
private theorem false_of_mem_support_of_comap_eq_top {A B : Scheme.{u}} (u : B ⟶ A)
    (I : A.IdealSheafData) (htop : I.comap u = ⊤) (y : ↥B) (hz : u.base y ∈ I.support) : False := by
  have hmem : y ∈ (I.comap u).support := Scheme.IdealSheafData.mem_support_comap.mpr hz
  rw [htop] at hmem
  exact false_of_mem_support_top y hmem

/- English proof (authored)
The comparison square at the last stages is a pullback of the original base morphism. The last-stage map is therefore flat by stability of flatness under base change.
-/
private theorem flat_lastMap {X X' : Scheme.{u}} {φ : X' ⟶ X}
    [AlgebraicGeometry.Flat φ] {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) : AlgebraicGeometry.Flat c.lastMap :=
  MorphismProperty.of_isPullback c.isPullback_lastMap.flip inferInstance

/- English proof (authored)
Induct on the stage number. The zero stage is isomorphic to the given Noetherian base scheme. At a successor stage within the length, the preceding stage is Noetherian by induction and its blowup is again Noetherian.
-/
private theorem isNoetherian_schemeAt_of_le_length {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (hX : AlgebraicGeometry.IsNoetherian X) (d : MarkedBlowupSequenceData p I m E) :
    ∀ i ≤ d.length, AlgebraicGeometry.IsNoetherian (d.obj i) := by
  have : AlgebraicGeometry.IsNoetherian X := hX
  intro i
  induction i with
  | zero =>
      intro _
      exact isNoetherian_of_iso d.toBlowupSequenceData.isoZero.symm
  | succ n ih =>
      intro hn
      have : AlgebraicGeometry.IsNoetherian (d.obj n) := ih (le_of_lt hn)
      exact isNoetherian_of_isBlowupAlongIdealSheaf (d.toBlowupSequenceData.isBlowup n hn)

/- English proof (authored)
Admissibility of the last center includes the condition that its ideal is proper. Hence this ideal differs from the unit ideal.
-/
private theorem centerAtLast_ne_top_of_isAdmissibleCenter {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (h : MarkedBlowupSequenceData.IsAdmissibleCenter s) : s.centerAtLast ≠ ⊤ := h.1

/- English proof (authored)
The iteration begins with the empty blowup sequence. At iteration zero this is still the sequence, so the length is zero.
-/
private theorem length_monomialIterateFromEmpty_zero (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) :
    (monomialIterateFromEmpty hinv T 0).length = 0 := emptyMarkedBlowupSequenceData_length _ _ _ _

/- English proof (authored)
Both single steps are blowups of their initial centers. The upper initial center is the pullback of the lower one along the flat stage-zero comparison. Flat base change of blowups gives a pullback square for the blowup morphisms. The initial identifications express the stage-zero comparison by the original base map, and the upper center is proper. These data give the comparison of the length-one sequences.
-/
private theorem nonempty_sequenceOfBlowupsPullback_of_length_eq_one {A B : Scheme.{u}} (φ : B ⟶ A)
    (t : BlowupSequenceData A) (t' : BlowupSequenceData B) (ht : t.length = 1) (ht' : t'.length = 1)
    (ψ : t'.obj 0 ⟶ t.obj 0)
    (hψ : t'.isoZero.hom ≫ φ ≫ t.isoZero.inv = ψ) (hflat : AlgebraicGeometry.Flat ψ)
    (hcen : t'.center 0 = (t.center 0).comap ψ) (hne : t'.center 0 ≠ ⊤) :
    Nonempty (SequenceOfBlowupsPullback φ t'.toSequenceOfBlowups t.toSequenceOfBlowups) := by
  have := hflat
  have hlt : (0 : ℕ) < t.length := by rw [ht]; omega
  have hlt' : (0 : ℕ) < t'.length := by rw [ht']; omega
  have hB : Blowup.IsBlowupAlongIdealSheaf (t.map 0) (t.center 0) := t.isBlowup 0 hlt
  have hB' : Blowup.IsBlowupAlongIdealSheaf (t'.map 0) ((t.center 0).comap ψ) := by
    have h := t'.isBlowup 0 hlt'
    rwa [hcen] at h
  obtain ⟨qq, -, hqq⟩ := hB.exists_isPullback_of_flat ψ hB'
  refine ⟨SequenceOfBlowupsPullback.ofLengthOne φ t t' ht ht' qq ?_ ?_ hne⟩
  · rw [hψ]
    exact hqq
  · rw [hψ]
    exact hcen

/- English proof (authored)
The admissible lower center appends a single blowup. Its pullback to the upper last stage is the unit ideal. Thus no upper point maps into the support of the lower center. The omitted-center construction compares the empty upper extension with this single lower step over the last-stage map. Concatenate that comparison with the existing one. Identifying the upper append of the empty sequence with the original upper sequence gives the required comparison.
-/
private theorem nonempty_sequenceOfBlowupsPullback_blowupAtCenter_of_comap_eq_top {k₁ k₂ : Type u}
    [Field k₁] [Field k₂] {X₁ X₂ : Scheme.{u}}
    {p₁ : X₁ ⟶ Spec (CommRingCat.of k₁)} {I₁ : X₁.IdealSheafData} {m₁ : ℕ}
    {E₁ : List X₁.IdealSheafData} {p₂ : X₂ ⟶ Spec (CommRingCat.of k₂)} {I₂ : X₂.IdealSheafData}
    {m₂ : ℕ} {E₂ : List X₂.IdealSheafData} (g : X₂ ⟶ X₁) (hg : AlgebraicGeometry.Flat g)
    (hinv : ComapIsoInvariance.{u}) (S : MarkedBlowupSequenceData p₁ I₁ m₁ E₁)
    (S' : MarkedBlowupSequenceData p₂ I₂ m₂ E₂) (hS : MarkedBlowupSequenceData.IsAdmissibleCenter S)
    (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups)
    (htop : (S.centerAtLast).comap c.lastMap = ⊤) :
    Nonempty (SequenceOfBlowupsPullback g S'.toSequenceOfBlowups (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) := by
  have := hg
  have : AlgebraicGeometry.Flat c.lastMap := flat_lastMap c
  have hmiss : ∀ i : ℕ, i < (S.monomialBlowupStep hS).toBlowupSequenceData.length →
      ∀ z : ↥((S.monomialBlowupStep hS).toBlowupSequenceData.obj i),
        z ∈ ((S.monomialBlowupStep hS).toBlowupSequenceData.center i).support →
        ∀ y : ↥(S'.obj S'.length),
          c.lastMap.base y ≠ ((S.monomialBlowupStep hS).toBlowupSequenceData.projectionToBase i).base z := by
    intro i hi z hz y heq
    have hlen : (S.monomialBlowupStep hS).toBlowupSequenceData.length = 1 :=
      MarkedBlowupSequenceData.monomialBlowupStep_length ..
    have hi0 : i = 0 := by omega
    subst hi0
    have hzz : ((S.monomialBlowupStep hS).toBlowupSequenceData.projectionToBase 0).base z ∈ S.centerAtLast.support := hz
    have hz2 : c.lastMap.base y ∈ S.centerAtLast.support := by
      rw [heq]
      exact hzz
    exact false_of_mem_support_of_comap_eq_top c.lastMap S.centerAtLast htop y hz2
  have hE0 : (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData.length = 0 := emptyMarkedBlowupSequenceData_length _ _ _ _
  have e := SequenceOfBlowupsPullback.ofCentersMissImage c.lastMap (S.monomialBlowupStep hS).toBlowupSequenceData hmiss
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData hE0
  have c2 := SequenceOfBlowupsPullback.concat S.toBlowupSequenceData (S.monomialBlowupStep hS).toBlowupSequenceData
    S'.toBlowupSequenceData
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData c e
  refine ⟨?_⟩
  rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S hS, MarkedBlowupSequenceData.append_toBlowupSequenceData]
  exact SequenceOfBlowupsPullback.ofConcatLengthZero g S'.toBlowupSequenceData
    (S.appendToBlowupSequenceData (S.monomialBlowupStep hS)).toSequenceOfBlowups
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData hE0 c2

/- English proof (authored)
Both last centers are admissible, so each appended step is a single blowup with a proper center. The last-stage map is flat by base change. The new stage-zero identifications are identities, so the given equality of the center ideals is the comparison required for the length-one pullback construction. Append the resulting comparison of single steps to the comparison of the given sequences to get the two extended sequences.
-/
private theorem nonempty_sequenceOfBlowupsPullback_blowupAtCenter {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    {X₁ X₂ : Scheme.{u}}
    {p₁ : X₁ ⟶ Spec (CommRingCat.of k₁)} {I₁ : X₁.IdealSheafData} {m₁ : ℕ}
    {E₁ : List X₁.IdealSheafData} {p₂ : X₂ ⟶ Spec (CommRingCat.of k₂)} {I₂ : X₂.IdealSheafData}
    {m₂ : ℕ} {E₂ : List X₂.IdealSheafData} (g : X₂ ⟶ X₁) (hg : AlgebraicGeometry.Flat g)
    (hinv : ComapIsoInvariance.{u}) (S : MarkedBlowupSequenceData p₁ I₁ m₁ E₁)
    (S' : MarkedBlowupSequenceData p₂ I₂ m₂ E₂) (hS : MarkedBlowupSequenceData.IsAdmissibleCenter S)
    (hS' : MarkedBlowupSequenceData.IsAdmissibleCenter S') (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups)
    (hcen : S'.centerAtLast = (S.centerAtLast).comap c.lastMap) :
    Nonempty (SequenceOfBlowupsPullback g (MarkedBlowupSequenceData.blowupAtCenter hinv S').toSequenceOfBlowups
      (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) := by
  have := hg
  have : AlgebraicGeometry.Flat c.lastMap := flat_lastMap c
  have h1 : (S'.monomialBlowupStep hS').toBlowupSequenceData.isoZero.hom ≫ c.lastMap ≫
      (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv
      = c.lastMap ≫ (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv :=
    Category.id_comp _
  have h2 : c.lastMap ≫ (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv = c.lastMap :=
    Category.comp_id _
  have hconj : (S'.monomialBlowupStep hS').toBlowupSequenceData.isoZero.hom ≫ c.lastMap ≫
      (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv = c.lastMap := h1.trans h2
  obtain ⟨e⟩ := nonempty_sequenceOfBlowupsPullback_of_length_eq_one c.lastMap
    (S.monomialBlowupStep hS).toBlowupSequenceData
    (S'.monomialBlowupStep hS').toBlowupSequenceData (MarkedBlowupSequenceData.monomialBlowupStep_length ..)
    (MarkedBlowupSequenceData.monomialBlowupStep_length ..) c.lastMap hconj
    (flat_lastMap c) hcen (centerAtLast_ne_top_of_isAdmissibleCenter S' hS')
  refine ⟨?_⟩
  rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S hS,
    MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S' hS',
    MarkedBlowupSequenceData.append_toBlowupSequenceData, MarkedBlowupSequenceData.append_toBlowupSequenceData]
  exact SequenceOfBlowupsPullback.concat S.toBlowupSequenceData (S.monomialBlowupStep hS).toBlowupSequenceData
    S'.toBlowupSequenceData (S'.monomialBlowupStep hS').toBlowupSequenceData c e

/- English proof (authored)
Replace the upper boundary by the directly pulled-back boundary. Admissibility and local monomiality survive this replacement, and the minimum size and center are unchanged because the nonunit entries are the same in order. Flatness and order preservation supply the component-compatible comparison. A positive upper minimum forces a positive lower minimum. For a positive lower minimum, either the upper minimum is zero or the lower invariant is weakly below the upper one. The lower center pulls back to the unit ideal if the upper minimum is zero or the invariant comparison is strict. If all entries agree, the chosen indices agree under the boundary index map. Then the upper minimum is positive and the upper center is the pullback of the lower one. Transfer these conclusions back to the given upper boundary.
-/
private theorem minIndexCard_ne_zero_and_monomialCenter_comap_of_flat (hGeom : MonomialGeometryHypotheses.{u})
    (Tn : MarkedIdealWithBoundary.{u})
    (Yj : Scheme.{u}) (k' : Type u) [instk' : Field k'] (qj : Yj ⟶ Spec (CommRingCat.of k'))
    (φ : Yj ⟶ Tn.scheme) (hφ : AlgebraicGeometry.Flat φ)
    (I' : Yj.IdealSheafData) (E2 : List Yj.IdealSheafData)
    (hTn : MonomialCenter.IsLocallyMonomialTriple Tn)
    (hTj : MonomialCenter.IsLocallyMonomialTriple (@MarkedIdealWithBoundary.mk k' instk' Yj qj I' Tn.mult E2))
    (hI' : I' = Tn.ideal.comap φ)
    (hE2 : MarkedIdealWithBoundary.SameNontrivialBoundary E2 (Tn.boundary.map fun D => D.comap φ))
    (hordφ : ∀ (A : Tn.scheme.IdealSheafData) (y : ↥Yj),
      orderAt (A.comap φ) y = orderAt A (φ y)) :
    (minIndexCard I' Tn.mult E2 ≠ 0 → minIndexCard Tn.ideal Tn.mult Tn.boundary ≠ 0) ∧
      (minIndexCard Tn.ideal Tn.mult Tn.boundary ≠ 0 →
        ((monomialCenter Tn.ideal Tn.mult Tn.boundary).comap φ = ⊤ ∨
          (minIndexCard I' Tn.mult E2 ≠ 0 ∧
            monomialCenter I' Tn.mult E2 = (monomialCenter Tn.ideal Tn.mult Tn.boundary).comap φ))) := by
  classical
  have := hφ
  subst hI'
  have htrip : (@MarkedIdealWithBoundary.mk k' instk' Yj qj (Tn.ideal.comap φ) Tn.mult E2).withBoundary
      (Tn.boundary.map fun D => D.comap φ) = Tn.pullbackOverField Yj k' qj φ :=
    MarkedIdealWithBoundary.mk_eq_mk Yj Tn.mult rfl rfl rfl
  have hTpb : MonomialCenter.IsLocallyMonomialTriple (Tn.pullbackOverField Yj k' qj φ) := by
    rw [← htrip]
    exact MonomialCenter.isLocallyMonomialTriple_withBoundary hGeom _ hTj _ hE2
  have hP : MonomialCenter.IsComponentCompatiblePullback Tn Yj k' qj φ :=
    MonomialCenter.IsComponentCompatiblePullback.of_flat hGeom Tn hTn.valid Yj k' qj φ hTpb.valid hordφ
  have hmin : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
      (Tn.pullbackOverField Yj k' qj φ).boundary = minIndexCard (Tn.ideal.comap φ) Tn.mult E2 :=
    (MonomialCenter.minIndexCard_eq_of_sameNontrivialBoundary (Tn.ideal.comap φ) Tn.mult hE2).symm
  have hcenpb : monomialCenter (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
      (Tn.pullbackOverField Yj k' qj φ).boundary = monomialCenter (Tn.ideal.comap φ) Tn.mult E2 :=
    (MonomialCenter.monomialCenter_eq_of_sameNontrivialBoundary (Tn.ideal.comap φ) Tn.mult hE2).symm
  refine ⟨?_, ?_⟩
  · intro hne
    have hne' : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
        (Tn.pullbackOverField Yj k' qj φ).boundary ≠ 0 := by
      rw [hmin]
      exact hne
    exact (MonomialCenter.minIndexCard_ne_zero_and_le_pullbackOverField hGeom Tn Yj k' qj φ hTn hTpb hP hne').1
  · intro h0
    by_cases hz : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
        (Tn.pullbackOverField Yj k' qj φ).boundary = 0
    · exact Or.inl (MonomialCenter.comap_monomialCenter_eq_top hGeom Tn Yj k' qj φ hTn hTpb hP h0
        (Or.inl hz))
    · have hle := (MonomialCenter.minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le hGeom Tn Yj k' qj φ hTn hTpb
        hP).resolve_left hz
      rw [MonomialCenter.centerInvariant_le_iff] at hle
      rcases hle with hlt | ⟨hm, hx, hs⟩
      · exact Or.inl (MonomialCenter.comap_monomialCenter_eq_top hGeom Tn Yj k' qj φ hTn hTpb hP h0
          (Or.inr hlt))
      · refine Or.inr ⟨?_, ?_⟩
        · rw [← hmin]
          exact hz
        · rw [← hcenpb]
          exact MonomialCenter.monomialCenter_pullbackOverField_eq_comap hGeom Tn Yj k' qj φ hTn hTpb hP
            hm.symm hx.symm
            (MonomialCenter.lexMaxIndices_pullbackOverField_eq_image Tn Yj k' qj φ hs)

/- English proof (authored)
The final comparison of the existing sequences is a pullback square, with a flat last-stage map. The transformed upper ideal is the pullback of the lower one, and its boundary has the same nonunit ideals in order as the pulled-back lower boundary. This follows from the comparison of marked transforms on the Noetherian stages. The assumed preservation of order applies to the final square. Use the flat center comparison on the final triples. Admissibility upstairs implies a positive upper minimum, hence a positive lower one. If the lower center is admissible, it has positive minimum. The center comparison either makes its pullback the unit ideal, allowing the single lower step to be omitted upstairs, or identifies it with the upper center at a positive upper minimum. In the latter case the upper center is admissible and the single steps on both sides extend the comparison.
-/
private theorem sequenceOfBlowupsPullback_blowupAtCenter_cases
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hg : AlgebraicGeometry.Flat g) (E' : List Y.IdealSheafData)
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E'))
    (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z))
    (S : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (S' : MarkedBlowupSequenceData (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary)
    (hTn : MonomialCenter.IsLocallyMonomialTriple (tripleAtLastBlowup T S))
    (hTj : MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLastBlowup (T.pullbackWithBoundary Y k' q g E') S'))
    (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups) :
    (MarkedBlowupSequenceData.IsAdmissibleCenter S' →
        minIndexCard (tripleAtLastBlowup T S).ideal (tripleAtLastBlowup T S).mult
          (tripleAtLastBlowup T S).boundary ≠ 0) ∧
      (MarkedBlowupSequenceData.IsAdmissibleCenter S →
        Nonempty (SequenceOfBlowupsPullback g S'.toSequenceOfBlowups
            (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) ∨
          (MarkedBlowupSequenceData.IsAdmissibleCenter S' ∧
            Nonempty (SequenceOfBlowupsPullback g
              (MarkedBlowupSequenceData.blowupAtCenter hinv S').toSequenceOfBlowups
              (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups))) := by
  classical
  have hfl1 : AlgebraicGeometry.Flat g := hg
  have hfl2 : @AlgebraicGeometry.Flat (T.pullbackWithBoundary Y k' q g E').scheme T.scheme g := hg
  have hflt : AlgebraicGeometry.Flat c.lastMap := flat_lastMap c
  have hN : ∀ i : ℕ, i ≤ S.length → AlgebraicGeometry.IsNoetherian (S.obj i) :=
    isNoetherian_schemeAt_of_le_length hT.valid.isNoetherian S
  have hN' : ∀ i : ℕ, i ≤ S'.length → AlgebraicGeometry.IsNoetherian (S'.obj i) :=
    isNoetherian_schemeAt_of_le_length hT'.valid.isNoetherian S'
  obtain ⟨hIdeal, hboundary⟩ := SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap S S' c rfl hE hN hN'
  have hsq : IsPullback c.lastMap (S'.proj S'.length) (S.proj S.length) g := by
    rw [MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups S S.length,
      MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups S' S'.length]
    exact c.isPullback_lastMap
  have hordφ : ∀ (A : (S.obj S.length).IdealSheafData) (y : ↥(S'.obj S'.length)),
      orderAt (A.comap c.lastMap) y = orderAt A (c.lastMap y) :=
    fun A y => hord (S.obj S.length) (S.proj S.length) (S.proj S.length ≫ T.structMap) rfl
      (S.ideal S.length) (S.boundary S.length) hTn.valid (S'.obj S'.length) c.lastMap
      (S'.proj S'.length) hsq A y
  have hminCard := minIndexCard_ne_zero_and_monomialCenter_comap_of_flat hGeom (tripleAtLastBlowup T S)
    (S'.obj S'.length) k' (S'.proj S'.length ≫ q) c.lastMap
    (flat_lastMap c) (S'.ideal S'.length) (S'.boundary S'.length)
    hTn hTj hIdeal hboundary hordφ
  refine ⟨fun hok' => hminCard.1
    (minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter (T.pullbackWithBoundary Y k' q g E') S' hok'), ?_⟩
  intro hok
  have h0 := minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T S hok
  rcases hminCard.2 h0 with hmiss | ⟨hne', hcenEq⟩
  · exact Or.inl
      (nonempty_sequenceOfBlowupsPullback_blowupAtCenter_of_comap_eq_top g hg hinv S S' hok c hmiss)
  · have hok' : MarkedBlowupSequenceData.IsAdmissibleCenter S' :=
      isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero hGeom (T.pullbackWithBoundary Y k' q g E') S'
        hTj hne'
    exact Or.inr ⟨hok', nonempty_sequenceOfBlowupsPullback_blowupAtCenter g hg hinv S S' hok hok' c hcenEq⟩

/- English proof (authored)
Induct on the number of lower steps up to the first stationary index. At zero take the two empty sequences, which compare over the base map and have no centers. At a successor, compare the preceding lower iterate with an upper iterate by induction. All earlier upper centers are admissible, and the preceding lower center is admissible since it occurs before the lower stationary index. Both final triples are locally monomial. The one-step comparison either extends only the lower sequence, keeping the upper index and its admissibility history, or extends both sequences by one admissible blowup. In the latter case add the new upper center to its history. This gives the claimed comparison and upper index.
-/
private theorem exists_sequenceOfBlowupsPullback_monomialIterateFromEmpty
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hg : AlgebraicGeometry.Flat g) (E' : List Y.IdealSheafData)
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E'))
    (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z))
    (n : ℕ) :
    n ≤ monomialStallIndexOfTriple hinv T →
    ∃ j : ℕ,
      (∀ j' : ℕ, j' < j →
        MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j')) ∧
      Nonempty (SequenceOfBlowupsPullback g
        (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j).toSequenceOfBlowups
        (monomialIterateFromEmpty hinv T n).toSequenceOfBlowups) := by
  have := hg
  induction n with
  | zero =>
    intro _
    refine ⟨0, fun j' hj' => absurd hj' (Nat.not_lt_zero j'), ⟨?_⟩⟩
    refine SequenceOfBlowupsPullback.ofCentersMissImage g (monomialIterateFromEmpty hinv T 0).toBlowupSequenceData ?_
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') 0).toBlowupSequenceData
      (length_monomialIterateFromEmpty_zero hinv (T.pullbackWithBoundary Y k' q g E'))
    intro i hi
    exact absurd hi (by rw [length_monomialIterateFromEmpty_zero hinv T]; exact Nat.not_lt_zero i)
  | succ n ih =>
    intro hn
    have hn' : n < monomialStallIndexOfTriple hinv T := lt_of_lt_of_le (Nat.lt_succ_self n) hn
    obtain ⟨j, hjstep, hc⟩ := ih (le_of_lt hn')
    obtain ⟨c⟩ := hc
    have hok : MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv T n) :=
      isAdmissibleCenter_of_lt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary n hn'
    rcases (sequenceOfBlowupsPullback_blowupAtCenter_cases hGeom hinv T Y k' q g hg E' hT hE hT' hord
      (monomialIterateFromEmpty hinv T n)
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT n)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv
        (T.pullbackWithBoundary Y k' q g E') hT' j) c).2 hok with h | ⟨hok', h⟩
    · exact ⟨j, hjstep, h⟩
    · refine ⟨j + 1, ?_, h⟩
      intro j' hj'
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with h1 | h1
      · exact hjstep j' h1
      · rw [h1]
        exact hok'

/- English proof (authored)
Apply the iterative comparison at the lower first stationary index, obtaining a comparable upper iterate whose earlier centers were all admissible. At the lower stationary index the minimum candidate size is zero. If the current upper center were admissible, the one-step comparison would force the lower minimum to be positive. Thus the current upper center is inadmissible, and this is the first stationary upper index. The two principalizations are the sequences at these stationary indices. The constructed comparison of the iterates therefore supplies the pullback relation for the principalizations.
-/
theorem monomialPrincipalization_isPullbackBlowupSequence_of_flat
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g] (E' : List Y.IdealSheafData)
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E'))
    (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z)) :
    IsPullbackBlowupSequence g
      (monomialPrincipalization hinv (T.pullbackWithBoundary Y k' q g E')).toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  classical
  have hg : AlgebraicGeometry.Flat g := inferInstance
  obtain ⟨j, hjstep, hc⟩ := exists_sequenceOfBlowupsPullback_monomialIterateFromEmpty hGeom hinv T Y k' q g hg E'
    hT hE hT' hord (monomialStallIndexOfTriple hinv T) le_rfl
  obtain ⟨c⟩ := hc
  have hstall : ¬ MarkedBlowupSequenceData.IsAdmissibleCenter
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j) := by
    intro hok'
    refine (sequenceOfBlowupsPullback_blowupAtCenter_cases hGeom hinv T Y k' q g hg E' hT hE hT' hord
      (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT
        (monomialStallIndexOfTriple hinv T))
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv
        (T.pullbackWithBoundary Y k' q g E') hT' j) c).1 hok' ?_
    exact minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero hGeom hinv T hT
  have hjeq : monomialStallIndex hinv (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary = j :=
    monomialStallIndex_eq_of_isStationaryAt hinv (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary j
      ((MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv
        (emptyMarkedBlowupSequenceData (T.pullbackWithBoundary Y k' q g E').structMap
          (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
          (T.pullbackWithBoundary Y k' q g E').boundary) j).mpr hstall) hjstep
  rw [monomialPrincipalization_apply, monomialPrincipalization_apply, monomialBlowupSeq_eq_monomialBlowupIterate,
    monomialBlowupSeq_eq_monomialBlowupIterate, hjeq]
  exact SequenceOfBlowupsPullback.isPullbackSequenceOfBlowups c

/- English proof (authored)
The indicated projection to the lower scheme is obtained by base change of the given smooth morphism. Smoothness is preserved by base change.
-/
private theorem smooth_fst_of_isPullback {X Y B Q : Scheme.{u}} {hm : Y ⟶ X}
    [AlgebraicGeometry.Smooth hm] {b : B ⟶ X} {a : Q ⟶ B} {b' : Q ⟶ Y}
    (hsq : IsPullback a b' b hm) : AlgebraicGeometry.Smooth a :=
  MorphismProperty.of_isPullback hsq.flip inferInstance

/- English proof (authored)
The given smooth morphism is flat, and at the original field its pullback triple agrees with the specified same-field construction. The boundary equality can be read in either direction. In every comparison square required by the flat theorem the map on the lower stage is a base change of the original smooth morphism, hence smooth. The lower structural morphism is smooth over a characteristic-zero field by admissibility. Order is preserved under such smooth pullback, which supplies the remaining hypothesis of the flat comparison theorem.
-/
theorem monomialPrincipalization_isPullbackBlowupSequence_of_smooth
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (hT' : MonomialCenter.IsLocallyMonomialTriple ((T.pullbackAlong Y q h).withBoundary E')) :
    IsPullbackBlowupSequence h
      (monomialPrincipalization hinv ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  have : AlgebraicGeometry.Flat h := inferInstance
  have hE2 : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap h) := hE.symm
  have hT2 : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y T.base q h E') := hT'
  have hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b h →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z) := by
    intro B b pB hbp IB EB hvalid Q a b' hsq A z
    have : CharZero T.base := hvalid.charZero
    have : AlgebraicGeometry.Smooth pB := hvalid.smooth
    have : AlgebraicGeometry.Smooth a := smooth_fst_of_isPullback hsq
    exact orderAt_comap T.base pB a A z
  exact monomialPrincipalization_isPullbackBlowupSequence_of_flat hGeom hinv T Y T.base q h E' hT hE2 hT2 hord

end FunctorialResolution.EmbeddedResolution

end
