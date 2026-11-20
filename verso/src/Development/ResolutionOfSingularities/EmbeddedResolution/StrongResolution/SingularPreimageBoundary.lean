import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformAvoidance
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineDetachedConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GenericPointsAvoidCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.CentersLieOverSingularLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SmoothLocusPreimageDense
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The underlying point map of a composite is obtained by applying the first point map and then applying the second.
-/
private theorem base_comp_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A) :
    (f ≫ g).base x = g.base (f.base x) := by simp

/- English proof (authored)
An open immersion identifies the source with an open subscheme of the target. Restricting to an open neighborhood does not change the stalk at a point of that neighborhood, so the stalk map is an isomorphism.
-/
private theorem isIso_stalkMap_of_isOpenImmersion {A B : Scheme.{u}} (f : A ⟶ B)
    [AlgebraicGeometry.IsOpenImmersion f] (x : ↥A) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap f x) := by
  infer_instance

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

/- English proof (authored)
Every morphism factors through the closed subscheme defined by its kernel ideal. Thus the image of the chosen source point belongs to the range of that closed subscheme’s inclusion, which is the kernel ideal’s support.
-/
private theorem base_apply_mem_support_ker {W Z : Scheme.{u}} (g : W ⟶ Z) (q : ↥W) :
    g.base q ∈ ((AlgebraicGeometry.Scheme.Hom.ker g).support : Set ↥Z) := by
  have hle : AlgebraicGeometry.Scheme.Hom.ker
        (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι ≤
      AlgebraicGeometry.Scheme.Hom.ker g :=
    le_of_eq (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _)
  have hfac : AlgebraicGeometry.IsClosedImmersion.lift
        (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι g hle ≫
      (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι = g :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
  exact ⟨(AlgebraicGeometry.IsClosedImmersion.lift
      (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι g hle).base q, by
    rw [← base_comp_apply, hfac]⟩

/- English proof (authored)
The point lies in the complement of the detached locus and maps into the ambient center. By the support formula for pullbacks, its lift to the complement therefore lies in the support of the restricted center ideal. Lift it further to the closed subscheme of that ideal. The composite from this closed subscheme to the full strict transform has kernel equal to the center ideal off the detached locus. Its image point lies in that kernel’s support.
-/
theorem mem_support_centerOffDetached_of_mem_support_ambientCenter (i : ℕ) (p : ↥(S.strictTransform i))
    (hp : p ∈ ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)))
    (hmem : (S.strictTransformι i).base p ∈ ((S.ambientCenter i).support : Set ↥(S.ambientLevel i))) :
    p ∈ (((S.centerOffDetached i).support : TopologicalSpace.Closeds ↥(S.strictTransform i)) :
      Set ↥(S.strictTransform i)) := by
  have hU : p ∈ S.discardedLocusClosureCompl i := hp
  have htrace : p ∈ ((S.comapAmbientCenter i).support : Set ↥(S.strictTransform i)) := by
    rw [S.comapAmbientCenter_eq i]
    exact Scheme.IdealSheafData.mem_support_comap.mpr hmem
  have hq0 : (⟨p, hU⟩ : ↥(S.discardedLocusClosureCompl i)) ∈
      ((((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).support :
        TopologicalSpace.Closeds ↥(S.discardedLocusClosureCompl i).toScheme) :
        Set ↥(S.discardedLocusClosureCompl i).toScheme) :=
    Scheme.IdealSheafData.mem_support_comap.mpr htrace
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι] at hq0
  obtain ⟨q, hq⟩ := hq0
  have hmain := base_apply_mem_support_ker
    (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫ (S.discardedLocusClosureCompl i).ι) q
  rw [base_comp_apply, hq] at hmain
  rw [S.centerOffDetached_eq i]
  exact hmain

/- English proof (authored)
Induct on the stage, with the initial case vacuous because no center has yet been encountered. At a successor, the point projects to the base through its image in the preceding strict transform. If its ambient image lies in the current center, the preceding strict-transform point lies in the complement of the detached locus because it comes from the next strict transform. It is therefore on the center off the detached locus, which maps into the original singular locus by hypothesis. If the ambient image avoids the current center, failure of successor avoidance means that this image failed to avoid an earlier center. The strict-transform square identifies the relevant preceding point, so induction puts its base image in the singular locus as well.
-/
private theorem forall_mem_smoothLocusComplement_of_not_avoidsCenters
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j))
    (hopen : ∀ j < S.ambientLength, IsOpen (S.discardedLocus j))
    (hcent : S.CentersLieOverSingularLocus) :
    ∀ (i : ℕ), i ≤ S.ambientLength → ∀ p : ↥(S.strictTransform i),
      ¬ S.toEmbeddedBlowupSequence.AvoidsCenters i ((S.strictTransformι i).base p) →
      (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p ∈
        ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  have hNl : ∀ m, m ≤ S.ambientLength → TopologicalSpace.NoetherianSpace ↥(S.ambientLevel m) := by
    intro m hm
    have := hN m hm
    infer_instance
  intro i
  induction i with
  | zero =>
      intro _ p hp
      exact absurd (S.toEmbeddedBlowupSequence.avoidsCenters_zero _) hp
  | succ j ih =>
      intro hj p hp
      have hjlt : j < S.ambientLength := Nat.lt_of_succ_le hj
      have hjle : j ≤ S.ambientLength := Nat.le_of_lt hjlt
      have hnj : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel j) := hNl j hjle
      have hNa : TopologicalSpace.NoetherianSpace ↥(S.strictTransform j) :=
        S.noetherianSpace_strictTransform j
      have hNl' : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (j + 1)) := hNl (j + 1) hj
      have key : (S.strictTransformι j).base ((S.strictTransformMap j).base p)
          = (S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base p) := by
        have h : (S.strictTransformMap j ≫ S.strictTransformι j).base p
            = (S.strictTransformι (j + 1) ≫ S.ambientBlowupMorphism j).base p := by
          rw [S.strictTransformMap_comp_strictTransformι j]
        simpa using h
      have hdown : (S.strictTransformToZero (j + 1) ≫ S.strictTransformZeroToBase).base p
          = (S.strictTransformToZero j ≫ S.strictTransformZeroToBase).base ((S.strictTransformMap j).base p) := by
        simp
      rw [hdown]
      by_cases hc : (S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base p) ∈
          ((S.ambientCenter j).support : Set ↥(S.ambientLevel j))
      · have hfc : (S.strictTransformMap j).base p ∈
            ((S.discardedLocusClosureCompl j : (S.strictTransform j).Opens) : Set ↥(S.strictTransform j)) :=
          S.range_strictTransformMap_subset_discardedLocusClosureCompl j hjlt hNa hNl' (hopen j hjlt) ⟨p, rfl⟩
        have hmem : (S.strictTransformι j).base ((S.strictTransformMap j).base p) ∈
            ((S.ambientCenter j).support : Set ↥(S.ambientLevel j)) := by
          rw [key]
          exact hc
        exact hcent j hjlt ((S.strictTransformMap j).base p)
          (S.mem_support_centerOffDetached_of_mem_support_ambientCenter j ((S.strictTransformMap j).base p)
            hfc hmem)
      · refine ih hjle ((S.strictTransformMap j).base p) ?_
        intro hcl
        have hcl' : S.toEmbeddedBlowupSequence.AvoidsCenters j ((S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base p)) := by
          rw [← key]
          exact hcl
        exact hp ((S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff j ((S.strictTransformι (j + 1)).base p)).mpr ⟨hc, hcl'⟩)

/- English proof (authored)
Apply the stagewise result to the given point. Its failure to avoid prior centers puts its image under the projection through stage zero in the complement of the smooth locus.
-/
theorem mem_smoothLocusComplement_of_not_avoidsCenters [AlgebraicGeometry.IsReduced Y]
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j))
    (hopen : ∀ j < S.ambientLength, IsOpen (S.discardedLocus j))
    (hcent : S.CentersLieOverSingularLocus)
    (i : ℕ) (hi : i ≤ S.ambientLength) (p : ↥(S.strictTransform i))
    (hp : ¬ S.toEmbeddedBlowupSequence.AvoidsCenters i ((S.strictTransformι i).base p)) :
    (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p ∈
      ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) :=
  forall_mem_smoothLocusComplement_of_not_avoidsCenters S hN hopen hcent i hi p hp

/- English proof (authored)
The image lies in the preceding support with the center removed, so the point belongs to the inverse image of that difference. It therefore belongs to its closure, which is the support of the strict-transform ideal.
-/
private theorem mem_support_strictTransform_of_mem_support_of_notMem_support {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    [AlgebraicGeometry.IsLocallyNoetherian X₁] (Z D : X.IdealSheafData) (x : ↥X₁)
    (hD : π.base x ∈ ((D.support : TopologicalSpace.Closeds ↥X) : Set ↥X))
    (hZ : π.base x ∉ ((Z.support : TopologicalSpace.Closeds ↥X) : Set ↥X)) :
    x ∈ (((FunctorialResolution.Blowup.strictTransform π Z D).support :
      TopologicalSpace.Closeds ↥X₁) : Set ↥X₁) := by
  rw [FunctorialResolution.EmbeddedResolution.support_strictTransform_eq_closure_preimage π Z D]
  exact subset_closure (Set.mem_preimage.mpr (Set.mem_sdiff_of_mem hD hZ))

/- English proof (authored)
Induct on the stage. Initial avoidance is vacuous. At a successor the point avoids all the new boundary, including the new exceptional divisor. This divisor is the pullback of the current center, so the image point avoids the center. If the image belonged to a prior boundary support, the original point, being off the center, would lie in the strict transform of that support. That strict transform is also a member of the new boundary, a contradiction. Hence the image avoids all prior boundary members and avoids the earlier centers by induction. Together these give successor avoidance.
-/
private theorem avoidsCenters_of_forall_notMem_support_boundary
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j)) :
    ∀ (i : ℕ), i ≤ S.principalizationSequence.length → ∀ x : ↥(S.principalizationSequence.schemeAt i),
      (∀ E ∈ S.principalizationSequence.boundary i,
        x ∉ ((E.support : TopologicalSpace.Closeds ↥(S.principalizationSequence.schemeAt i)) :
          Set ↥(S.principalizationSequence.schemeAt i))) →
      S.toEmbeddedBlowupSequence.AvoidsCenters i x := by
  intro i
  induction i with
  | zero =>
      intro _ x _
      exact S.toEmbeddedBlowupSequence.avoidsCenters_zero x
  | succ i ih =>
      intro hi x hx
      have hilt : i < S.principalizationSequence.length := hi
      have hbnd := S.principalizationSequence.boundary_succ_eq_map_strictTransform_append i hilt
      have hexc : S.principalizationSequence.exceptionalIdeal i ∈ S.principalizationSequence.boundary (i + 1) := by
        rw [hbnd]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      have hnc : ((S.principalizationSequence.transitionMapSucc i).base x) ∉
          (((S.principalizationSequence.center i).support :
            TopologicalSpace.Closeds ↥(S.principalizationSequence.schemeAt i)) : Set ↥(S.principalizationSequence.schemeAt i)) := by
        intro hmem
        refine hx _ hexc ?_
        rw [S.principalizationSequence.exceptionalIdeal_eq i]
        exact Scheme.IdealSheafData.mem_support_comap.mpr hmem
      refine (S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff i x).mpr ⟨hnc, ?_⟩
      refine ih (Nat.le_of_succ_le hi) ((S.principalizationSequence.transitionMapSucc i).base x) ?_
      intro E hE hmem
      have hlocNoeth : AlgebraicGeometry.IsLocallyNoetherian (S.principalizationSequence.schemeAt (i + 1)) :=
        (hN (i + 1) hi).toIsLocallyNoetherian
      refine hx (FunctorialResolution.Blowup.strictTransform (S.principalizationSequence.transitionMapSucc i) (S.principalizationSequence.center i) E)
        ?_ ?_
      · rw [hbnd]
        exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨E, hE, rfl⟩))
      · exact @_root_.FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.mem_support_strictTransform_of_mem_support_of_notMem_support (S.principalizationSequence.schemeAt i) (S.principalizationSequence.schemeAt (i + 1))
          (S.principalizationSequence.transitionMapSucc i) hlocNoeth (S.principalizationSequence.center i) E x hmem hnc

/- English proof (authored)
Use the inductive boundary avoidance result on the ambient stage of these principalization data. It identifies avoidance of every current boundary support as sufficient for avoiding all earlier centers.
-/
theorem avoidsCenters_of_forall_notMem_boundary
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j))
    (i : ℕ) (hi : i ≤ S.ambientLength) (x : ↥(S.ambientLevel i))
    (hx : ∀ E ∈ S.boundary i, x ∉ ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) :
      Set ↥(S.ambientLevel i))) :
    S.toEmbeddedBlowupSequence.AvoidsCenters i x :=
  avoidsCenters_of_forall_notMem_support_boundary S hN i hi x hx

/- English proof (authored)
If both ring maps are isomorphisms, the composite is inverted by composing their inverses in reverse order.
-/
private theorem isIso_comp_of_isIso_commRingCat {P Q R : CommRingCat.{u}} (u : P ⟶ Q) (v : Q ⟶ R)
    (hu : CategoryTheory.IsIso u) (hv : CategoryTheory.IsIso v) :
    CategoryTheory.IsIso (u ≫ v) := by
  have := hu
  have := hv
  infer_instance

/- English proof (authored)
Compose the isomorphic composite with the inverse of the second map. The second map and its inverse cancel, leaving the first map as a composite of isomorphisms.
-/
private theorem isIso_of_isIso_comp_right {P Q R : CommRingCat.{u}} (u : P ⟶ Q) (v : Q ⟶ R)
    (hv : CategoryTheory.IsIso v) (huv : CategoryTheory.IsIso (u ≫ v)) :
    CategoryTheory.IsIso u := by
  have := hv
  have := huv
  have h : u = (u ≫ v) ≫ CategoryTheory.inv v := by
    rw [CategoryTheory.Category.assoc, CategoryTheory.IsIso.hom_inv_id,
      CategoryTheory.Category.comp_id]
  rw [h]
  infer_instance

/- English proof (authored)
The stalk map of the composite is the stalk map of the second scheme morphism followed by that of the first. Since the second ring map in this composite is an isomorphism and the composite is an isomorphism, the first ring map is an isomorphism by cancellation.
-/
private theorem isIso_stalkMap_of_isIso_stalkMap_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A)
    (hf : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap f x))
    (hfg : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap (f ≫ g) x)) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap g (f.base x)) := by
  rw [AlgebraicGeometry.Scheme.Hom.stalkMap_comp] at hfg
  exact isIso_of_isIso_comp_right _ _ hf hfg

/- English proof (authored)
Pull the equality back along the inverse isomorphism. Successive pullback along the isomorphism and its inverse is pullback along the identity, leaving the original ideal sheaves equal.
-/
private theorem idealSheafData_comap_injective_of_isIso {A B : Scheme.{u}} (φ : A ⟶ B)
    [CategoryTheory.IsIso φ] (I J : B.IdealSheafData)
    (h : I.comap φ = J.comap φ) : I = J := by
  have h2 : (I.comap φ).comap (CategoryTheory.inv φ)
      = (J.comap φ).comap (CategoryTheory.inv φ) := by rw [h]
  rwa [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    CategoryTheory.IsIso.inv_hom_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id] at h2

/- English proof (authored)
The strict-transform ideal is the kernel of the closed immersion formed from the original ideal pulled back over the center complement, followed by inclusion of that open into the blowup. Restricting this kernel to the open gives the kernel of the closed immersion itself. This is exactly the restricted pullback of the original ideal.
-/
private theorem strictTransform_comap_ι_eq_comap_restrict {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [TopologicalSpace.NoetherianSpace ↥X₁] :
    (FunctorialResolution.Blowup.strictTransform π Z D).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))
      = (D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl) := by
  have := (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).isEmbedding.toIsInducing.noetherianSpace
  rw [FunctorialResolution.EmbeddedResolution.strictTransform_eq_ker_restrict π Z D]
  exact FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp _ _

/- English proof (authored)
Restrict the ambient map to the given open, where it is an isomorphism. Composing the restricted upper closed immersion with that isomorphism gives a closed immersion into the lower open. Its kernel agrees with the restricted lower closed immersion’s kernel, because their pullbacks along the ambient isomorphism agree by hypothesis and such pullback is injective. Equal kernels give an isomorphism between these two closed subschemes of the open. Compatibility of the original square and cancellation of the lower closed immersion identify the prescribed morphism on the upper open with that isomorphism followed by inclusion of the corresponding lower open. Thus it is an open immersion.
-/
private theorem isOpenImmersion_preimage_ι_comp_of_ker_comap_eq {X X₁ A₀ A₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (ι₀ : A₀ ⟶ X) (ι₁ : A₁ ⟶ X₁) (m : A₁ ⟶ A₀) (V : X.Opens)
    [AlgebraicGeometry.IsClosedImmersion ι₀] [AlgebraicGeometry.IsClosedImmersion ι₁]
    [CategoryTheory.IsIso (π ∣_ V)]
    (hm : m ≫ ι₀ = ι₁ ≫ π)
    (hker : (AlgebraicGeometry.Scheme.Hom.ker ι₁).comap (Scheme.Opens.ι (π ⁻¹ᵁ V))
      = ((AlgebraicGeometry.Scheme.Hom.ker ι₀).comap (Scheme.Opens.ι V)).comap (π ∣_ V)) :
    AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ m) := by
  have hciα : AlgebraicGeometry.IsClosedImmersion ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) :=
    inferInstance
  have hk1 := FunctorialResolution.EmbeddedResolution.ker_comap_ι_eq_ker_morphismRestrict ι₁ (π ⁻¹ᵁ V)
  have hk0 := FunctorialResolution.EmbeddedResolution.ker_comap_ι_eq_ker_morphismRestrict ι₀ V
  have hcomp := FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion (ι₁ ∣_ (π ⁻¹ᵁ V)) (π ∣_ V)
  have hkereq : AlgebraicGeometry.Scheme.Hom.ker ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V))
      = AlgebraicGeometry.Scheme.Hom.ker (ι₀ ∣_ V) := by
    refine idealSheafData_comap_injective_of_isIso (π ∣_ V) _ _ ?_
    rw [hcomp, ← hk1, hker, hk0]
  have hle : AlgebraicGeometry.Scheme.Hom.ker (ι₀ ∣_ V)
      ≤ AlgebraicGeometry.Scheme.Hom.ker ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) := le_of_eq hkereq.symm
  have hfac := AlgebraicGeometry.IsClosedImmersion.lift_fac (ι₀ ∣_ V)
    ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle
  have hIso : CategoryTheory.IsIso (AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
      ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) :=
    AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq _ _ _ hfac hkereq
  have hmono : (Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ m) ≫ ι₀
      = ((AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
          ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ Scheme.Opens.ι (ι₀ ⁻¹ᵁ V)) ≫ ι₀ := by
    calc (Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ m) ≫ ι₀
        = Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ (m ≫ ι₀) := CategoryTheory.Category.assoc _ _ _
      _ = Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ (ι₁ ≫ π) := by rw [hm]
      _ = (Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ ι₁) ≫ π :=
          (CategoryTheory.Category.assoc _ _ _).symm
      _ = ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ Scheme.Opens.ι (π ⁻¹ᵁ V)) ≫ π := by
          rw [AlgebraicGeometry.morphismRestrict_ι]
      _ = (ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (Scheme.Opens.ι (π ⁻¹ᵁ V) ≫ π) :=
          CategoryTheory.Category.assoc _ _ _
      _ = (ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ ((π ∣_ V) ≫ Scheme.Opens.ι V) := by
          rw [AlgebraicGeometry.morphismRestrict_ι]
      _ = ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) ≫ Scheme.Opens.ι V :=
          (CategoryTheory.Category.assoc _ _ _).symm
      _ = ((AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
            ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ (ι₀ ∣_ V)) ≫ Scheme.Opens.ι V := by
          rw [hfac]
      _ = (AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
            ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ ((ι₀ ∣_ V) ≫ Scheme.Opens.ι V) :=
          CategoryTheory.Category.assoc _ _ _
      _ = (AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
            ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ (Scheme.Opens.ι (ι₀ ⁻¹ᵁ V) ≫ ι₀) := by
          rw [AlgebraicGeometry.morphismRestrict_ι]
      _ = ((AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V)
            ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ Scheme.Opens.ι (ι₀ ⁻¹ᵁ V)) ≫ ι₀ :=
          (CategoryTheory.Category.assoc _ _ _).symm
  have hfin := (CategoryTheory.cancel_mono ι₀).mp hmono
  rw [hfin]
  infer_instance

/- English proof (authored)
The projection from the successor stage to the ambient base factors through the preceding stage by the current blowdown. Composing with the ambient base’s map to the field gives the displayed compatibility.
-/
private theorem ambientBlowupMorphism_comp_schemeAtToSpec (j : ℕ) :
    S.ambientBlowupMorphism j ≫ S.schemeAtToSpec j = S.schemeAtToSpec (j + 1) := by
  have h := FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_succ S.ambientBlowups j
  rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, AffineSpacePrincipalizationData.schemeAtToSpec_def, h,
    CategoryTheory.Category.assoc]

/- English proof (authored)
Induct on the stage. The initial projection is the identity. At a successor the induction hypothesis calculates the composite to the field through the preceding strict transform. The strict-transform transition commutes with the ambient blowdown, and that blowdown commutes with the structure maps to the field. Thus the composite is the new strict-transform inclusion followed by the new ambient structure map.
-/
private theorem strictTransformToZero_comp_schemeAtToSpec (i : ℕ) :
    S.strictTransformToZero i ≫ S.strictTransformι 0 ≫ S.schemeAtToSpec 0 = S.strictTransformι i ≫ S.schemeAtToSpec i := by
  induction i with
  | zero => rw [AffineSpacePrincipalizationData.strictTransformToZero_zero, CategoryTheory.Category.id_comp]
  | succ j ih =>
      rw [AffineSpacePrincipalizationData.strictTransformToZero_succ, CategoryTheory.Category.assoc, ih,
        ← CategoryTheory.Category.assoc, S.strictTransformMap_comp_strictTransformι j, CategoryTheory.Category.assoc,
        ambientBlowupMorphism_comp_schemeAtToSpec S j]

/- English proof (authored)
The map of the discarded piece to the original scheme factors through its strict transform and the initial strict transform. The initial map followed by the morphism to the field agrees with the ambient initial structural map on the strict transform. The successive strict-transform maps commute with all structural maps to the field, so substitution gives the stated equality.
-/
private theorem detachedToBase_comp_eq_discardedι_comp_schemeAtToSpec (i : ℕ) :
    S.detachedToBase i ≫ pY = S.discardedι i ≫ S.strictTransformι i ≫ S.schemeAtToSpec i := by
  rw [AffineSpacePrincipalizationData.detachedToBase_def, CategoryTheory.Category.assoc,
    CategoryTheory.Category.assoc, AffineSpacePrincipalizationData.strictTransformZeroToBase_comp,
    ← strictTransformToZero_comp_schemeAtToSpec S i]

/- English proof (authored)
At zero the projection is the identity. At a successor, avoidance places the point above the complement of the current center, where the ambient blowdown is an isomorphism and the new strict-transform ideal is the pullback of the preceding one. The strict-transform map is therefore an open immersion near the point by the restricted kernel comparison. It induces an isomorphism on the stalk. The image point downstairs avoids all earlier centers by the avoidance criterion and the commuting square. By induction its projection to zero induces an isomorphism on stalks as well. The stalk map of the composite to zero is a composite of these isomorphisms.
-/
private theorem isIso_stalkMap_strictTransformToZero_of_avoidsCenters
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j)) (j : ℕ) :
    j ≤ S.ambientLength → ∀ a : ↥(S.strictTransform j),
      S.toEmbeddedBlowupSequence.AvoidsCenters j ((S.strictTransformι j).base a) →
      CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap (S.strictTransformToZero j) a) := by
  induction j with
  | zero =>
      intro _ a _
      rw [AffineSpacePrincipalizationData.strictTransformToZero_zero]
      exact isIso_stalkMap_of_isOpenImmersion
        (CategoryTheory.CategoryStruct.id (S.strictTransform 0)) a
  | succ j ih =>
      intro hj a ha
      have hjlt : j < S.ambientLength := Nat.lt_of_succ_le hj
      have hNoe : AlgebraicGeometry.IsNoetherian (S.ambientLevel (j + 1)) := hN (j + 1) hj
      have hNs : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (j + 1)) := inferInstance
      obtain ⟨hnc, hcl⟩ := (S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff j ((S.strictTransformι (j + 1)).base a)).mp ha
      have haO : a ∈ (S.strictTransformι (j + 1) ⁻¹ᵁ
          (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl)) := hnc
      have hiso : CategoryTheory.IsIso
          (S.ambientBlowupMorphism j ∣_ ((S.ambientCenter j).support.compl)) :=
        S.toEmbeddedBlowupSequence.isIso_blowdown_restrict_ambientCenterSupportCompl j hjlt
      have hker : (AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι (j + 1))).comap
            (Scheme.Opens.ι (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl))
          = ((AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι j)).comap
              (Scheme.Opens.ι ((S.ambientCenter j).support.compl))).comap
              (S.ambientBlowupMorphism j ∣_ ((S.ambientCenter j).support.compl)) := by
        rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
          AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, S.strictTransformIdeal_succ j]
        exact strictTransform_comap_ι_eq_comap_restrict (S.ambientBlowupMorphism j) (S.ambientCenter j) (S.strictTransformIdeal j)
      have hoi : AlgebraicGeometry.IsOpenImmersion
          (Scheme.Opens.ι (S.strictTransformι (j + 1) ⁻¹ᵁ
            (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl)) ≫ S.strictTransformMap j) :=
        isOpenImmersion_preimage_ι_comp_of_ker_comap_eq (S.ambientBlowupMorphism j) (S.strictTransformι j) (S.strictTransformι (j + 1))
          (S.strictTransformMap j) ((S.ambientCenter j).support.compl) (S.strictTransformMap_comp_strictTransformι j) hker
      have h2 : CategoryTheory.IsIso
          (AlgebraicGeometry.Scheme.Hom.stalkMap (S.strictTransformMap j) a) :=
        isIso_stalkMap_of_isIso_stalkMap_comp
          (Scheme.Opens.ι (S.strictTransformι (j + 1) ⁻¹ᵁ
            (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl))) (S.strictTransformMap j)
          ⟨a, haO⟩ (isIso_stalkMap_of_isOpenImmersion _ _) (isIso_stalkMap_of_isOpenImmersion _ _)
      have hb : (S.strictTransformι j).base ((S.strictTransformMap j).base a)
          = (S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base a) := by
        have h := congrArg (fun f : S.strictTransform (j + 1) ⟶ S.ambientLevel j => f.base a)
          (S.strictTransformMap_comp_strictTransformι j)
        simpa using h
      have hclj : S.toEmbeddedBlowupSequence.AvoidsCenters j ((S.strictTransformι j).base ((S.strictTransformMap j).base a)) := by
        rw [hb]
        exact hcl
      have hih := ih (Nat.le_of_succ_le hj) ((S.strictTransformMap j).base a) hclj
      rw [AffineSpacePrincipalizationData.strictTransformToZero_succ, AlgebraicGeometry.Scheme.Hom.stalkMap_comp]
      exact isIso_comp_of_isIso_commRingCat _ _ hih h2

/- English proof (authored)
An isomorphism of rings is formally smooth. A map from its target across a nilpotent quotient lifts by transporting the given map from its source along the inverse isomorphism.
-/
private theorem formallySmooth_of_isIso {A B : CommRingCat.{u}} (ψ : A ⟶ B)
    [CategoryTheory.IsIso ψ] : (CommRingCat.Hom.hom ψ).FormallySmooth := by
  have hb : Function.Bijective (CommRingCat.Hom.hom ψ) :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso ψ
  exact RingHom.FormallySmooth.of_bijective hb

/- English proof (authored)
Compose the formally smooth map from the hypothesis with the inverse isomorphism, which is formally smooth. The isomorphisms cancel, so formal smoothness of the composite gives formal smoothness of the original first map.
-/
private theorem formallySmooth_of_formallySmooth_comp_isIso {R A B : CommRingCat.{u}} (φ : R ⟶ A) (ψ : A ⟶ B)
    [CategoryTheory.IsIso ψ]
    (h : (CommRingCat.Hom.hom (φ ≫ ψ)).FormallySmooth) :
    (CommRingCat.Hom.hom φ).FormallySmooth := by
  have h1 : (φ ≫ ψ) ≫ CategoryTheory.inv ψ = φ := by
    rw [CategoryTheory.Category.assoc, CategoryTheory.IsIso.hom_inv_id,
      CategoryTheory.Category.comp_id]
  rw [← h1, CommRingCat.hom_comp]
  exact RingHom.FormallySmooth.comp h (formallySmooth_of_isIso (CategoryTheory.inv ψ))

/- English proof (authored)
The discarded subscheme is the clopen subscheme of the reduced strict transform, so its inclusion induces a stalk isomorphism. The projection to the initial strict transform induces a stalk isomorphism by center avoidance, and the initial map to the base is an open immersion, giving another stalk isomorphism. Their composite is the discarded piece’s map to the base, so its stalk map is an isomorphism. The discarded piece is smooth over the field. Thus the composite from the base field to its local ring is formally smooth. Cancelling the stalk isomorphism gives formal smoothness of the structural stalk map at the image in the base. This places the base image in the smooth locus.
-/
theorem notMem_smoothLocusComplement_detachedToBase_of_avoidsCenters [AlgebraicGeometry.IsReduced Y]
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j))
    (hopen : ∀ j < S.ambientLength, IsOpen (S.discardedLocus j))
    (hsmooth : S.DetachedSmooth)
    (i : ℕ) (hi : i < S.ambientLength) (q : ↥(S.discardedSubscheme i))
    (hq : S.toEmbeddedBlowupSequence.AvoidsCenters i ((S.strictTransformι i).base ((S.discardedι i).base q))) :
    (S.detachedToBase i).base q ∉
      ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  intro hmem
  have hred : AlgebraicGeometry.IsReduced (S.strictTransform i) :=
    S.isReduced_strictTransform hN i (le_of_lt hi)
  have hnl : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel i) := by
    have := hN i (le_of_lt hi)
    infer_instance
  have hna : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform i
  obtain ⟨e, he⟩ := S.exists_iso_discardedSubscheme_discardedLocusOpens i hna (hopen i hi)
  have hfi : AlgebraicGeometry.IsOpenImmersion (S.discardedι i) := by
    rw [← he]
    infer_instance
  have hab : AlgebraicGeometry.IsOpenImmersion S.strictTransformZeroToBase :=
    FunctorialResolution.EmbeddedResolution.isOpenImmersion_strictTransformZeroToBase S
  have hchain := isIso_stalkMap_strictTransformToZero_of_avoidsCenters S hN i (le_of_lt hi) ((S.discardedι i).base q) hq
  have hsm : AlgebraicGeometry.Smooth (S.detachedToBase i ≫ pY) := by
    rw [detachedToBase_comp_eq_discardedι_comp_schemeAtToSpec S i]
    exact hsmooth i hi
  have hstq : CategoryTheory.IsIso
      (AlgebraicGeometry.Scheme.Hom.stalkMap (S.detachedToBase i) q) := by
    have h1 : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap S.strictTransformZeroToBase
        ((S.strictTransformToZero i).base ((S.discardedι i).base q))) := isIso_stalkMap_of_isOpenImmersion _ _
    have h2 : CategoryTheory.IsIso
        (AlgebraicGeometry.Scheme.Hom.stalkMap (S.discardedι i) q) :=
      isIso_stalkMap_of_isOpenImmersion _ _
    rw [AffineSpacePrincipalizationData.detachedToBase_def, AlgebraicGeometry.Scheme.Hom.stalkMap_comp,
      AlgebraicGeometry.Scheme.Hom.stalkMap_comp]
    exact isIso_comp_of_isIso_commRingCat _ _ (isIso_comp_of_isIso_commRingCat _ _ h1 hchain) h2
  have htop : (S.detachedToBase i ≫ pY).smoothLocus = ⊤ :=
    AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff.mpr hsm
  have hmemq : q ∈ (S.detachedToBase i ≫ pY).smoothLocus := by
    rw [htop]
    exact TopologicalSpace.Opens.mem_top q
  have hfs := AlgebraicGeometry.Scheme.Hom.mem_smoothLocus.mp hmemq
  rw [AlgebraicGeometry.Scheme.Hom.stalkMap_comp] at hfs
  have hfs2 : (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap pY
      ((S.detachedToBase i).base q))).FormallySmooth :=
    formallySmooth_of_formallySmooth_comp_isIso _ _ hfs
  have hin : (S.detachedToBase i).base q ∈ pY.smoothLocus :=
    AlgebraicGeometry.Scheme.Hom.mem_smoothLocus.mpr hfs2
  exact hmem hin

/- English proof (authored)
A point outside every ambient boundary support avoids all earlier centers by the boundary avoidance theorem. The stalk argument for such points then shows that its image in the original scheme belongs to the smooth locus.
-/
theorem notMem_smoothLocusComplement_detachedToBase_of_notMem_boundary [AlgebraicGeometry.IsReduced Y]
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j))
    (hopen : ∀ j < S.ambientLength, IsOpen (S.discardedLocus j))
    (hsmooth : S.DetachedSmooth)
    (i : ℕ) (hi : i < S.ambientLength) (q : ↥(S.discardedSubscheme i))
    (hq : ∀ E ∈ S.boundary i,
      (S.strictTransformι i).base ((S.discardedι i).base q) ∉
        ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i))) :
    (S.detachedToBase i).base q ∉
      ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  have hclear : S.toEmbeddedBlowupSequence.AvoidsCenters i ((S.strictTransformι i).base ((S.discardedι i).base q)) :=
    avoidsCenters_of_forall_notMem_boundary S hN i (le_of_lt hi)
      ((S.strictTransformι i).base ((S.discardedι i).base q)) hq
  exact notMem_smoothLocusComplement_detachedToBase_of_avoidsCenters S hN hopen hsmooth i hi q hclear

end AffineSpacePrincipalizationData

/- English proof (authored)
At stage zero the boundary is empty. At a successor, a boundary member is the new exceptional divisor or the strict transform of a previous boundary member. In the first case the image point lies on the current center because the exceptional support is its inverse image. In the second, the strict-transform support is contained in the pullback of the preceding support, so the image belongs to the preceding boundary and fails earlier avoidance by induction. Either case contradicts avoidance through the successor stage.
-/
private theorem principalizationSequence_not_avoidsCenters_of_mem_boundary {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    ∀ (i : ℕ), i ≤ S.principalizationSequence.length →
      ∀ E : (S.principalizationSequence.schemeAt i).IdealSheafData, E ∈ S.principalizationSequence.boundary i →
        ∀ x : ↥(S.principalizationSequence.schemeAt i), x ∈ (E.support : Set ↥(S.principalizationSequence.schemeAt i)) →
          ¬ S.toEmbeddedBlowupSequence.AvoidsCenters i x := by
  intro i
  induction i with
  | zero =>
      intro _ E hE x _ _
      rw [S.principalizationSequence.boundary_zero] at hE
      simp at hE
  | succ i ih =>
      intro hi E hE x hx hcl
      have hilt : i < S.principalizationSequence.length := hi
      rw [S.principalizationSequence.boundary_succ_eq_map_strictTransform_append i hilt, List.mem_append] at hE
      have hcl' := (S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff i x).mp hcl
      rcases hE with hE | hE
      · obtain ⟨E', hE', rfl⟩ := List.mem_map.mp hE
        have hmem : x ∈ ((E'.comap (S.principalizationSequence.transitionMapSucc i)).support :
            Set ↥(S.principalizationSequence.schemeAt (i + 1))) :=
          AlgebraicGeometry.Scheme.IdealSheafData.support_antitone
            (FunctorialResolution.EmbeddedResolution.comap_le_strictTransform (S.principalizationSequence.transitionMapSucc i)
              (S.principalizationSequence.center i) E') hx
        have hmem2 : (S.principalizationSequence.transitionMapSucc i).base x ∈
            (E'.support : Set ↥(S.principalizationSequence.schemeAt i)) :=
          OpenImmersionRestriction.mem_support_of_mem_support_comap (S.principalizationSequence.transitionMapSucc i) E' x hmem
        exact ih (Nat.le_of_succ_le hi) E' hE' _ hmem2 hcl'.2
      · rw [List.mem_singleton] at hE
        subst hE
        rw [S.principalizationSequence.exceptionalIdeal_eq i] at hx
        have hmem2 : (S.principalizationSequence.transitionMapSucc i).base x ∈
            ((S.principalizationSequence.center i).support : Set ↥(S.principalizationSequence.schemeAt i)) :=
          OpenImmersionRestriction.mem_support_of_mem_support_comap (S.principalizationSequence.transitionMapSucc i)
            (S.principalizationSequence.center i) x hx
        exact hcl'.1 hmem2

/- English proof (authored)
Use the inductive boundary result for the principalization sequence of the given affine-space data. The boundary, ambient stage, and avoidance predicate are those of that sequence.
-/
theorem not_avoidsCenters_of_mem_support_boundary (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY]
    (i : ℕ) (hi : i ≤ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength)
    (E : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i).IdealSheafData)
    (hE : E ∈ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i)
    (x : ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i))
    (hx : x ∈ ((E.support : TopologicalSpace.Closeds
        ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) :
      Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i))) :
    ¬ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence.AvoidsCenters i x :=
  principalizationSequence_not_avoidsCenters_of_mem_boundary (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) i hi E hE
    x hx

/- English proof (authored)
A point of the discarded piece whose ambient image is on the boundary lies in the support of one boundary member. This implies failure of center avoidance. Because the original centers off the detached locus lie over singular points, the earlier induction on failure of center avoidance sends the point in the strict transform to the singular locus. The discarded piece’s map to the base factors through that point, giving the claimed containment.
-/
theorem boundary_preimage_subset_smoothLocusComplement_preimage (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    (pY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    (hopen : ∀ j < (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength,
      IsOpen ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedLocus j))
    (hcent : (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).CentersLieOverSingularLocus)
    (i : ℕ) (hi : i < (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength) :
    ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i ≫
          (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base ⁻¹'
        (⋃ E ∈ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i,
          ((E.support : TopologicalSpace.Closeds
              ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) :
            Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i))) ⊆
      ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).detachedToBase i).base ⁻¹'
        ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  intro q hq
  have hq' : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i ≫
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base q ∈
      ⋃ E ∈ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i,
        ((E.support : TopologicalSpace.Closeds
            ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) :
          Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) := hq
  obtain ⟨E, hE, hmem⟩ := Set.mem_iUnion₂.mp hq'
  have hbase : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i ≫
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base q
      = ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base
          (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base q) :=
    base_comp_apply _ _ q
  rw [hbase] at hmem
  have hnc := not_avoidsCenters_of_mem_support_boundary A hemb hsnc hsm k Y pY i (le_of_lt hi) E hE
    (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base
      (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base q)) hmem
  have hsing := (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).mem_smoothLocusComplement_of_not_avoidsCenters
    (isNoetherian_ambientLevel_ofAffine A hemb hsnc hsm k Y pY) hopen hcent i (le_of_lt hi)
    (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base q) hnc
  show ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).detachedToBase i).base q ∈
    ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y)
  rw [AffineSpacePrincipalizationData.detachedToBase_def, base_comp_apply]
  exact hsing

/- English proof (authored)
One inclusion sends points on the ambient boundary to the original singular locus using the center condition. For the converse, suppose a point of the discarded piece lies over the singular locus but its ambient image lies in no boundary support. It then avoids all preceding centers. The local-ring comparison and smoothness of the discarded piece force its image to lie in the smooth locus, a contradiction. This proves equality of the two inverse images.
-/
theorem detachedSingularPreimageEqBoundary_ofAffine (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    (pY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    (hopen : ∀ j < (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength,
      IsOpen ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedLocus j))
    (hsmooth : (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedSmooth)
    (hcent : (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).CentersLieOverSingularLocus) :
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).DetachedSingularPreimageEqBoundary := by
  intro i hi
  refine Set.Subset.antisymm ?_
    (boundary_preimage_subset_smoothLocusComplement_preimage A hemb hsnc hsm k Y pY hopen hcent i hi)
  intro q hq
  by_contra hcon
  have hboundary : ∀ E ∈ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i,
      ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base
          (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base q) ∉
        ((E.support : TopologicalSpace.Closeds
            ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) :
          Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)) := by
    intro E hE hmem
    refine hcon ?_
    have hb := base_comp_apply
      ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i)
      ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i) q
    simp only [Set.mem_preimage, hb]
    exact Set.mem_iUnion₂.mpr ⟨E, hE, hmem⟩
  exact (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y
      pY).notMem_smoothLocusComplement_detachedToBase_of_notMem_boundary
    (isNoetherian_ambientLevel_ofAffine A hemb hsnc hsm k Y pY) hopen hsmooth i hi q hboundary hq

/- English proof (authored)
For any affine input the discarded loci are open and the discarded subschemes are smooth by hypothesis. The induced sequence’s centers lie over the singular locus, so restriction to the strict-transform summand gives that property for its centers off the detached loci. Apply the equality of inverse images for these affine principalization data at every relevant stage.
-/
theorem affineDetachedSingularPreimageEqBoundary_of_centersLieOverSing (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u})
    (hiso : EmbeddedPrincipalizationDiscardedLocusIsOpen A hemb hsnc hsm)
    (hsmooth : AffineDetachedSmooth A hemb hsnc hsm)
    (hPrincipalization : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm)
    (hcent : AffineCentersLieOverSingularLocus A hemb hsnc hsm hPrincipalization) :
    AffineDetachedSingularPreimageEqBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  refine detachedSingularPreimageEqBoundary_ofAffine A hemb hsnc hsm k Y pY (hiso k Y pY)
    (hsmooth k Y pY) ?_
  exact AffineSpacePrincipalizationData.centersLieOverSingularLocus_of_inducedCentersLieOverSingularLocus
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) (hPrincipalization k Y pY) (hcent k Y pY)

end FunctorialResolution.EmbeddedResolution

end
