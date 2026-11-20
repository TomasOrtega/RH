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

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem base_comp_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A) :
    (f ≫ g).base x = g.base (f.base x) := by simp

/- English proof (translation)
Use `infer_instance`.
-/
private theorem isIso_stalkMap_of_isOpenImmersion {A B : Scheme.{u}} (f : A ⟶ B)
    [AlgebraicGeometry.IsOpenImmersion f] (x : ↥A) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap f x) := by
  infer_instance

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

/- English proof (translation)
Establish `hle : AlgebraicGeometry.Scheme.Hom.ker (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι ≤ AlgebraicGeometry.Scheme.Hom.ker g` using `le_of_eq (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _)`. Establish `hfac : AlgebraicGeometry.IsClosedImmersion.lift (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι g hle ≫ (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι = g` using `AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _`. Rewrite using `[← AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]`. Conclude with `⟨(AlgebraicGeometry.IsClosedImmersion.lift (AlgebraicGeometry.Scheme.Hom.ker g).subschemeι g hle).base q, by`. Rewrite using `[← base_comp_apply, hfac]⟩`.
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

/- English proof (translation)
Establish `hU : p ∈ S.discardedLocusClosureCompl i` using `hp`. Establish `htrace : p ∈ ((S.comapAmbientCenter i).support : Set ↥(S.strictTransform i))`. Rewrite using `[S.comapAmbientCenter_eq i]`. Conclude with `Scheme.IdealSheafData.mem_support_comap.mpr hmem`. Establish `hq0 : (⟨p, hU⟩ : ↥(S.discardedLocusClosureCompl i)) ∈ ((((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).support : TopologicalSpace.Closeds ↥(S.discardedLocusClosureCompl i).toScheme) : Set ↥(S.discardedLocusClosureCompl i).toScheme)` using `Scheme.IdealSheafData.mem_support_comap.mpr htrace`.

Rewrite `hq0` using `[← AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]`. Take `⟨q, hq⟩` from `hq0`. Establish `hmain` using `base_apply_mem_support_ker (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫ (S.discardedLocusClosureCompl i).ι) q`. Rewrite `hmain` using `[base_comp_apply, hq]`. Rewrite using `[S.centerOffDetached_eq i]`.

Conclude with `hmain`.
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

/- English proof (translation)
Establish `hNl : ∀ m, m ≤ S.ambientLength → TopologicalSpace.NoetherianSpace ↥(S.ambientLevel m)`. Introduce `m hm`. Use `hN m hm` as an intermediate fact. Use `infer_instance`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ p hp`. Conclude with `absurd (S.toEmbeddedBlowupSequence.avoidsCenters_zero _) hp`. Consider the case `succ j ih`.

Introduce `hj p hp`. Establish `hjlt : j < S.ambientLength` using `Nat.lt_of_succ_le hj`. Establish `hjle : j ≤ S.ambientLength` using `Nat.le_of_lt hjlt`. Establish `hnj : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel j)` using `hNl j hjle`. Establish `hNa : TopologicalSpace.NoetherianSpace ↥(S.strictTransform j)` using `S.noetherianSpace_strictTransform j`.

Establish `hNl' : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (j + 1))` using `hNl (j + 1) hj`. Establish `key : (S.strictTransformι j).base ((S.strictTransformMap j).base p) = (S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base p)`. Establish `h : (S.strictTransformMap j ≫ S.strictTransformι j).base p = (S.strictTransformι (j + 1) ≫ S.ambientBlowupMorphism j).base p`. Rewrite using `[S.strictTransformMap_comp_strictTransformι j]`. Simplify using `using h`.

Establish `hdown : (S.strictTransformToZero (j + 1) ≫ S.strictTransformZeroToBase).base p = (S.strictTransformToZero j ≫ S.strictTransformZeroToBase).base ((S.strictTransformMap j).base p)`. Simplify using the standard rewrite rules. Rewrite using `[hdown]`. Distinguish the cases in `hc : (S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base p) ∈ ((S.ambientCenter j).support : Set ↥(S.ambientLevel j))`. Establish `hfc : (S.strictTransformMap j).base p ∈ ((S.discardedLocusClosureCompl j : (S.strictTransform j).Opens) : Set ↥(S.strictTransform j))` using `S.range_strictTransformMap_subset_discardedLocusClosureCompl j hjlt hNa hNl' (hopen j hjlt) ⟨p, rfl⟩`.

Establish `hmem : (S.strictTransformι j).base ((S.strictTransformMap j).base p) ∈ ((S.ambientCenter j).support : Set ↥(S.ambientLevel j))`. Rewrite using `[key]`. Conclude with `hc`. Conclude with `hcent j hjlt ((S.strictTransformMap j).base p) (S.mem_support_centerOffDetached_of_mem_support_ambientCenter j ((S.strictTransformMap j).base p) hfc hmem)`. Use `ih hjle ((S.strictTransformMap j).base p) ?_` and prove the remaining obligations.

Introduce `hcl`. Establish `hcl' : S.toEmbeddedBlowupSequence.AvoidsCenters j ((S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base p))`. Rewrite using `[← key]`. Conclude with `hcl`. Conclude with `hp ((S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff j ((S.strictTransformι (j + 1)).base p)).mpr ⟨hc, hcl'⟩)`.
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

/- English proof (translation)
The claim follows from `forall_mem_smoothLocusComplement_of_not_avoidsCenters S hN hopen hcent i hi p hp`.
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

/- English proof (translation)
Rewrite using `[FunctorialResolution.EmbeddedResolution.support_strictTransform_eq_closure_preimage π Z D]`. Conclude with `subset_closure (Set.mem_preimage.mpr (Set.mem_sdiff_of_mem hD hZ))`.
-/
private theorem mem_support_strictTransform_of_mem_support_of_notMem_support {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    [AlgebraicGeometry.IsLocallyNoetherian X₁] (Z D : X.IdealSheafData) (x : ↥X₁)
    (hD : π.base x ∈ ((D.support : TopologicalSpace.Closeds ↥X) : Set ↥X))
    (hZ : π.base x ∉ ((Z.support : TopologicalSpace.Closeds ↥X) : Set ↥X)) :
    x ∈ (((FunctorialResolution.Blowup.strictTransform π Z D).support :
      TopologicalSpace.Closeds ↥X₁) : Set ↥X₁) := by
  rw [FunctorialResolution.EmbeddedResolution.support_strictTransform_eq_closure_preimage π Z D]
  exact subset_closure (Set.mem_preimage.mpr (Set.mem_sdiff_of_mem hD hZ))

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ x _`. Conclude with `S.toEmbeddedBlowupSequence.avoidsCenters_zero x`.

Consider the case `succ i ih`. Introduce `hi x hx`. Establish `hilt : i < S.principalizationSequence.length` using `hi`. Establish `hbnd` using `S.principalizationSequence.boundary_succ_eq_map_strictTransform_append i hilt`. Establish `hexc : S.principalizationSequence.exceptionalIdeal i ∈ S.principalizationSequence.boundary (i + 1)`.

Rewrite using `[hbnd]`. Conclude with `List.mem_append.mpr (Or.inr (List.mem_singleton_self _))`. Establish `hnc : ((S.principalizationSequence.transitionMapSucc i).base x) ∉ (((S.principalizationSequence.center i).support : TopologicalSpace.Closeds ↥(S.principalizationSequence.schemeAt i)) : Set ↥(S.principalizationSequence.schemeAt i))`. Introduce `hmem`. Use `hx _ hexc ?_` and prove the remaining obligations.

Rewrite using `[S.principalizationSequence.exceptionalIdeal_eq i]`. Conclude with `Scheme.IdealSheafData.mem_support_comap.mpr hmem`. Use `(S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff i x).mpr ⟨hnc, ?_⟩` and prove the remaining obligations. Use `ih (Nat.le_of_succ_le hi) ((S.principalizationSequence.transitionMapSucc i).base x) ?_` and prove the remaining obligations. Introduce `E hE hmem`.

Establish `hlocNoeth : AlgebraicGeometry.IsLocallyNoetherian (S.principalizationSequence.schemeAt (i + 1))` using `(hN (i + 1) hi).toIsLocallyNoetherian`. Use `hx (FunctorialResolution.Blowup.strictTransform (S.principalizationSequence.transitionMapSucc i) (S.principalizationSequence.center i) E) ?_ ?_` and prove the remaining obligations. Rewrite using `[hbnd]`. Conclude with `List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨E, hE, rfl⟩))`. Conclude with `@_root_.FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.mem_support_strictTransform_of_mem_support_of_notMem_support (S.principalizationSequence.schemeAt i) (S.principalizationSequence.schemeAt (i + 1)) (S.principalizationSequence.transitionMapSucc i) hloc …`.
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

/- English proof (translation)
The claim follows from `avoidsCenters_of_forall_notMem_support_boundary S hN i hi x hx`.
-/
theorem avoidsCenters_of_forall_notMem_boundary
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j))
    (i : ℕ) (hi : i ≤ S.ambientLength) (x : ↥(S.ambientLevel i))
    (hx : ∀ E ∈ S.boundary i, x ∉ ((E.support : TopologicalSpace.Closeds ↥(S.ambientLevel i)) :
      Set ↥(S.ambientLevel i))) :
    S.toEmbeddedBlowupSequence.AvoidsCenters i x :=
  avoidsCenters_of_forall_notMem_support_boundary S hN i hi x hx

/- English proof (translation)
Use `hu` as an intermediate fact. Use `hv` as an intermediate fact. Use `infer_instance`.
-/
private theorem isIso_comp_of_isIso_commRingCat {P Q R : CommRingCat.{u}} (u : P ⟶ Q) (v : Q ⟶ R)
    (hu : CategoryTheory.IsIso u) (hv : CategoryTheory.IsIso v) :
    CategoryTheory.IsIso (u ≫ v) := by
  have := hu
  have := hv
  infer_instance

/- English proof (translation)
Use `hv` as an intermediate fact. Use `huv` as an intermediate fact. Establish `h : u = (u ≫ v) ≫ CategoryTheory.inv v`. Rewrite using `[CategoryTheory.Category.assoc, CategoryTheory.IsIso.hom_inv_id, CategoryTheory.Category.comp_id]`. Rewrite using `[h]`.

Use `infer_instance`.
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

/- English proof (translation)
Rewrite `hfg` using `[AlgebraicGeometry.Scheme.Hom.stalkMap_comp]`. Conclude with `isIso_of_isIso_comp_right _ _ hf hfg`.
-/
private theorem isIso_stalkMap_of_isIso_stalkMap_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A)
    (hf : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap f x))
    (hfg : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap (f ≫ g) x)) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap g (f.base x)) := by
  rw [AlgebraicGeometry.Scheme.Hom.stalkMap_comp] at hfg
  exact isIso_of_isIso_comp_right _ _ hf hfg

/- English proof (translation)
Establish `h2 : (I.comap φ).comap (CategoryTheory.inv φ) = (J.comap φ).comap (CategoryTheory.inv φ)` using `by rw [h]`. Rewrite `h2` using `[← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, CategoryTheory.IsIso.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`. Then use the resulting hypothesis.
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

/- English proof (translation)
Use `(Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).isEmbedding.toIsInducing.noetherianSpace` as an intermediate fact. Rewrite using `[FunctorialResolution.EmbeddedResolution.strictTransform_eq_ker_restrict π Z D]`. Conclude with `FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp _ _`.
-/
private theorem strictTransform_comap_ι_eq_comap_restrict {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [TopologicalSpace.NoetherianSpace ↥X₁] :
    (FunctorialResolution.Blowup.strictTransform π Z D).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))
      = (D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl) := by
  have := (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).isEmbedding.toIsInducing.noetherianSpace
  rw [FunctorialResolution.EmbeddedResolution.strictTransform_eq_ker_restrict π Z D]
  exact FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp _ _

/- English proof (translation)
Establish `hciα : AlgebraicGeometry.IsClosedImmersion ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V))` using `inferInstance`. Establish `hk1` using `FunctorialResolution.EmbeddedResolution.ker_comap_ι_eq_ker_morphismRestrict ι₁ (π ⁻¹ᵁ V)`. Establish `hk0` using `FunctorialResolution.EmbeddedResolution.ker_comap_ι_eq_ker_morphismRestrict ι₀ V`. Establish `hcomp` using `FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion (ι₁ ∣_ (π ⁻¹ᵁ V)) (π ∣_ V)`. Establish `hkereq : AlgebraicGeometry.Scheme.Hom.ker ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) = AlgebraicGeometry.Scheme.Hom.ker (ι₀ ∣_ V)`.

Use `idealSheafData_comap_injective_of_isIso (π ∣_ V) _ _ ?_` and prove the remaining obligations. Rewrite using `[hcomp, ← hk1, hker, hk0]`. Establish `hle : AlgebraicGeometry.Scheme.Hom.ker (ι₀ ∣_ V) ≤ AlgebraicGeometry.Scheme.Hom.ker ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V))` using `le_of_eq hkereq.symm`. Establish `hfac` using `AlgebraicGeometry.IsClosedImmersion.lift_fac (ι₀ ∣_ V) ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle`. Establish `hIso : CategoryTheory.IsIso (AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V) ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle)` using `AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq _ _ _ hfac hkereq`.

Establish `hmono : (Scheme.Opens.ι (ι₁ ⁻¹ᵁ (π ⁻¹ᵁ V)) ≫ m) ≫ ι₀ = ((AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V) ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ Scheme.Opens.ι (ι₀ ⁻¹ᵁ V)) ≫ ι₀`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[AlgebraicGeometry.morphismRestrict_ι]`. Use `_ = (ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (Scheme.Opens.ι (π ⁻¹ᵁ V) ≫ π) := CategoryTheory.Category.assoc _ _ _`. Use `_ = (ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ ((π ∣_ V) ≫ Scheme.Opens.ι V) := by`.

Rewrite using `[AlgebraicGeometry.morphismRestrict_ι]`. Use `_ = ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) ≫ Scheme.Opens.ι V := (CategoryTheory.Category.assoc _ _ _).symm`. Use `_ = ((AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V) ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ (ι₀ ∣_ V)) ≫ Scheme.Opens.ι V := by`. Rewrite using `[hfac]`. Use `_ = (AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V) ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ ((ι₀ ∣_ V) ≫ Scheme.Opens.ι V) := CategoryTheory.Category.assoc _ _ _`.

Use `_ = (AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V) ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ (Scheme.Opens.ι (ι₀ ⁻¹ᵁ V) ≫ ι₀) := by`. Rewrite using `[AlgebraicGeometry.morphismRestrict_ι]`. Use `_ = ((AlgebraicGeometry.IsClosedImmersion.lift (ι₀ ∣_ V) ((ι₁ ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) hle) ≫ Scheme.Opens.ι (ι₀ ⁻¹ᵁ V)) ≫ ι₀ := (CategoryTheory.Category.assoc _ _ _).symm`. Establish `hfin` using `(CategoryTheory.cancel_mono ι₀).mp hmono`. Rewrite using `[hfin]`.

Use `infer_instance`.
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

/- English proof (translation)
Establish `h` using `FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_succ S.ambientBlowups j`. Rewrite using `[AffineSpacePrincipalizationData.schemeAtToSpec_def, AffineSpacePrincipalizationData.schemeAtToSpec_def, h, CategoryTheory.Category.assoc]`.
-/
private theorem ambientBlowupMorphism_comp_schemeAtToSpec (j : ℕ) :
    S.ambientBlowupMorphism j ≫ S.schemeAtToSpec j = S.schemeAtToSpec (j + 1) := by
  have h := FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_succ S.ambientBlowups j
  rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, AffineSpacePrincipalizationData.schemeAtToSpec_def, h,
    CategoryTheory.Category.assoc]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => rw [AffineSpacePrincipalizationData.strictTransformToZero_zero, CategoryTheory.Category.id_comp]`. Consider the case `succ j ih`. Rewrite using `[AffineSpacePrincipalizationData.strictTransformToZero_succ, CategoryTheory.Category.assoc, ih, ← CategoryTheory.Category.assoc, S.strictTransformMap_comp_strictTransformι j, CategoryTheory.Category.assoc, ambientBlowupMorphism_comp_schemeAtToSpec S j]`.
-/
private theorem strictTransformToZero_comp_schemeAtToSpec (i : ℕ) :
    S.strictTransformToZero i ≫ S.strictTransformι 0 ≫ S.schemeAtToSpec 0 = S.strictTransformι i ≫ S.schemeAtToSpec i := by
  induction i with
  | zero => rw [AffineSpacePrincipalizationData.strictTransformToZero_zero, CategoryTheory.Category.id_comp]
  | succ j ih =>
      rw [AffineSpacePrincipalizationData.strictTransformToZero_succ, CategoryTheory.Category.assoc, ih,
        ← CategoryTheory.Category.assoc, S.strictTransformMap_comp_strictTransformι j, CategoryTheory.Category.assoc,
        ambientBlowupMorphism_comp_schemeAtToSpec S j]

/- English proof (translation)
Rewrite using `[AffineSpacePrincipalizationData.detachedToBase_def, CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, AffineSpacePrincipalizationData.strictTransformZeroToBase_comp, ← strictTransformToZero_comp_schemeAtToSpec S i]`.
-/
private theorem detachedToBase_comp_eq_discardedι_comp_schemeAtToSpec (i : ℕ) :
    S.detachedToBase i ≫ pY = S.discardedι i ≫ S.strictTransformι i ≫ S.schemeAtToSpec i := by
  rw [AffineSpacePrincipalizationData.detachedToBase_def, CategoryTheory.Category.assoc,
    CategoryTheory.Category.assoc, AffineSpacePrincipalizationData.strictTransformZeroToBase_comp,
    ← strictTransformToZero_comp_schemeAtToSpec S i]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ a _`. Rewrite using `[AffineSpacePrincipalizationData.strictTransformToZero_zero]`. Conclude with `isIso_stalkMap_of_isOpenImmersion (CategoryTheory.CategoryStruct.id (S.strictTransform 0)) a`.

Consider the case `succ j ih`. Introduce `hj a ha`. Establish `hjlt : j < S.ambientLength` using `Nat.lt_of_succ_le hj`. Establish `hNoe : AlgebraicGeometry.IsNoetherian (S.ambientLevel (j + 1))` using `hN (j + 1) hj`. Establish `hNs : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (j + 1))` using `inferInstance`.

Take `⟨hnc, hcl⟩` from `(S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff j ((S.strictTransformι (j + 1)).base a)).mp ha`. Establish `haO : a ∈ (S.strictTransformι (j + 1) ⁻¹ᵁ (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl))` using `hnc`. Establish `hiso : CategoryTheory.IsIso (S.ambientBlowupMorphism j ∣_ ((S.ambientCenter j).support.compl))` using `S.toEmbeddedBlowupSequence.isIso_blowdown_restrict_ambientCenterSupportCompl j hjlt`. Establish `hker : (AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι (j + 1))).comap (Scheme.Opens.ι (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl)) = ((AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι j)).comap (Scheme.Opens.ι ((S.ambientCenter j).support.compl))) …`. Rewrite using `[AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, S.strictTransformIdeal_succ j]`.

Conclude with `strictTransform_comap_ι_eq_comap_restrict (S.ambientBlowupMorphism j) (S.ambientCenter j) (S.strictTransformIdeal j)`. Establish `hoi : AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι (S.strictTransformι (j + 1) ⁻¹ᵁ (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl)) ≫ S.strictTransformMap j)` using `isOpenImmersion_preimage_ι_comp_of_ker_comap_eq (S.ambientBlowupMorphism j) (S.strictTransformι j) (S.strictTransformι (j + 1)) (S.strictTransformMap j) ((S.ambientCenter j).support.compl) (S.strictTransformMap_comp_strictTransformι j) hker`. Establish `h2 : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap (S.strictTransformMap j) a)` using `isIso_stalkMap_of_isIso_stalkMap_comp (Scheme.Opens.ι (S.strictTransformι (j + 1) ⁻¹ᵁ (S.ambientBlowupMorphism j ⁻¹ᵁ (S.ambientCenter j).support.compl))) (S.strictTransformMap j) ⟨a, haO⟩ (isIso_stalkMap_of_isOpenImmersion _ _) (isIso_stalkMap_of_isOpenImmersion _ _)`. Establish `hb : (S.strictTransformι j).base ((S.strictTransformMap j).base a) = (S.ambientBlowupMorphism j).base ((S.strictTransformι (j + 1)).base a)`. Establish `h` using `congrArg (fun f : S.strictTransform (j + 1) ⟶ S.ambientLevel j => f.base a) (S.strictTransformMap_comp_strictTransformι j)`.

Simplify using `using h`. Establish `hclj : S.toEmbeddedBlowupSequence.AvoidsCenters j ((S.strictTransformι j).base ((S.strictTransformMap j).base a))`. Rewrite using `[hb]`. Conclude with `hcl`. Establish `hih` using `ih (Nat.le_of_succ_le hj) ((S.strictTransformMap j).base a) hclj`.

Rewrite using `[AffineSpacePrincipalizationData.strictTransformToZero_succ, AlgebraicGeometry.Scheme.Hom.stalkMap_comp]`. Conclude with `isIso_comp_of_isIso_commRingCat _ _ hih h2`.
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

/- English proof (translation)
Establish `hb : Function.Bijective (CommRingCat.Hom.hom ψ)` using `CategoryTheory.ConcreteCategory.bijective_of_isIso ψ`. Conclude with `RingHom.FormallySmooth.of_bijective hb`.
-/
private theorem formallySmooth_of_isIso {A B : CommRingCat.{u}} (ψ : A ⟶ B)
    [CategoryTheory.IsIso ψ] : (CommRingCat.Hom.hom ψ).FormallySmooth := by
  have hb : Function.Bijective (CommRingCat.Hom.hom ψ) :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso ψ
  exact RingHom.FormallySmooth.of_bijective hb

/- English proof (translation)
Establish `h1 : (φ ≫ ψ) ≫ CategoryTheory.inv ψ = φ`. Rewrite using `[CategoryTheory.Category.assoc, CategoryTheory.IsIso.hom_inv_id, CategoryTheory.Category.comp_id]`. Rewrite using `[← h1, CommRingCat.hom_comp]`. Conclude with `RingHom.FormallySmooth.comp h (formallySmooth_of_isIso (CategoryTheory.inv ψ))`.
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

/- English proof (translation)
Introduce `hmem`. Establish `hred : AlgebraicGeometry.IsReduced (S.strictTransform i)` using `S.isReduced_strictTransform hN i (le_of_lt hi)`. Establish `hnl : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel i)`. Use `hN i (le_of_lt hi)` as an intermediate fact. Use `infer_instance`.

Establish `hna : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)` using `S.noetherianSpace_strictTransform i`. Take `⟨e, he⟩` from `S.exists_iso_discardedSubscheme_discardedLocusOpens i hna (hopen i hi)`. Establish `hfi : AlgebraicGeometry.IsOpenImmersion (S.discardedι i)`. Rewrite using `[← he]`. Use `infer_instance`.

Establish `hab : AlgebraicGeometry.IsOpenImmersion S.strictTransformZeroToBase` using `FunctorialResolution.EmbeddedResolution.isOpenImmersion_strictTransformZeroToBase S`. Establish `hchain` using `isIso_stalkMap_strictTransformToZero_of_avoidsCenters S hN i (le_of_lt hi) ((S.discardedι i).base q) hq`. Establish `hsm : AlgebraicGeometry.Smooth (S.detachedToBase i ≫ pY)`. Rewrite using `[detachedToBase_comp_eq_discardedι_comp_schemeAtToSpec S i]`. Conclude with `hsmooth i hi`.

Establish `hstq : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap (S.detachedToBase i) q)`. Establish `h1 : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap S.strictTransformZeroToBase ((S.strictTransformToZero i).base ((S.discardedι i).base q)))` using `isIso_stalkMap_of_isOpenImmersion _ _`. Establish `h2 : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Hom.stalkMap (S.discardedι i) q)` using `isIso_stalkMap_of_isOpenImmersion _ _`. Rewrite using `[AffineSpacePrincipalizationData.detachedToBase_def, AlgebraicGeometry.Scheme.Hom.stalkMap_comp, AlgebraicGeometry.Scheme.Hom.stalkMap_comp]`. Conclude with `isIso_comp_of_isIso_commRingCat _ _ (isIso_comp_of_isIso_commRingCat _ _ h1 hchain) h2`.

Establish `htop : (S.detachedToBase i ≫ pY).smoothLocus = ⊤` using `AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff.mpr hsm`. Establish `hmemq : q ∈ (S.detachedToBase i ≫ pY).smoothLocus`. Rewrite using `[htop]`. Conclude with `TopologicalSpace.Opens.mem_top q`. Establish `hfs` using `AlgebraicGeometry.Scheme.Hom.mem_smoothLocus.mp hmemq`.

Rewrite `hfs` using `[AlgebraicGeometry.Scheme.Hom.stalkMap_comp]`. Establish `hfs2 : (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap pY ((S.detachedToBase i).base q))).FormallySmooth` using `formallySmooth_of_formallySmooth_comp_isIso _ _ hfs`. Establish `hin : (S.detachedToBase i).base q ∈ pY.smoothLocus` using `AlgebraicGeometry.Scheme.Hom.mem_smoothLocus.mpr hfs2`. Conclude with `hmem hin`.
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

/- English proof (translation)
Establish `hclear : S.toEmbeddedBlowupSequence.AvoidsCenters i ((S.strictTransformι i).base ((S.discardedι i).base q))` using `avoidsCenters_of_forall_notMem_boundary S hN i (le_of_lt hi) ((S.strictTransformι i).base ((S.discardedι i).base q)) hq`. Conclude with `notMem_smoothLocusComplement_detachedToBase_of_avoidsCenters S hN hopen hsmooth i hi q hclear`.
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

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ E hE x _ _`. Rewrite `hE` using `[S.principalizationSequence.boundary_zero]`.

Simplify using `at hE`. Consider the case `succ i ih`. Introduce `hi E hE x hx hcl`. Establish `hilt : i < S.principalizationSequence.length` using `hi`. Rewrite `hE` using `[S.principalizationSequence.boundary_succ_eq_map_strictTransform_append i hilt, List.mem_append]`.

Establish `hcl'` using `(S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff i x).mp hcl`. Break down `hE with hE | hE` into its components or cases. Take `⟨E', hE', rfl⟩` from `List.mem_map.mp hE`. Establish `hmem : x ∈ ((E'.comap (S.principalizationSequence.transitionMapSucc i)).support : Set ↥(S.principalizationSequence.schemeAt (i + 1)))` using `AlgebraicGeometry.Scheme.IdealSheafData.support_antitone (FunctorialResolution.EmbeddedResolution.comap_le_strictTransform (S.principalizationSequence.transitionMapSucc i) (S.principalizationSequence.center i) E') hx`. Establish `hmem2 : (S.principalizationSequence.transitionMapSucc i).base x ∈ (E'.support : Set ↥(S.principalizationSequence.schemeAt i))` using `OpenImmersionRestriction.mem_support_of_mem_support_comap (S.principalizationSequence.transitionMapSucc i) E' x hmem`.

Conclude with `ih (Nat.le_of_succ_le hi) E' hE' _ hmem2 hcl'.2`. Rewrite `hE` using `[List.mem_singleton]`. Substitute `hE` using the available equality. Rewrite `hx` using `[S.principalizationSequence.exceptionalIdeal_eq i]`. Establish `hmem2 : (S.principalizationSequence.transitionMapSucc i).base x ∈ ((S.principalizationSequence.center i).support : Set ↥(S.principalizationSequence.schemeAt i))` using `OpenImmersionRestriction.mem_support_of_mem_support_comap (S.principalizationSequence.transitionMapSucc i) (S.principalizationSequence.center i) x hx`.

Conclude with `hcl'.1 hmem2`.
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

/- English proof (translation)
The claim follows from `principalizationSequence_not_avoidsCenters_of_mem_boundary (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) i hi E hE x hx`.
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

/- English proof (translation)
Introduce `q hq`. Establish `hq' : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i ≫ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base q ∈ ⋃ E ∈ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i, ((E.support : …` using `hq`. Take `⟨E, hE, hmem⟩` from `Set.mem_iUnion₂.mp hq'`. Establish `hbase : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i ≫ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base q = ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base ((( …` using `base_comp_apply _ _ q`. Rewrite `hmem` using `[hbase]`.

Establish `hnc` using `not_avoidsCenters_of_mem_support_boundary A hemb hsnc hsm k Y pY i (le_of_lt hi) E hE (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base q)) hmem`. Establish `hsing` using `(AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).mem_smoothLocusComplement_of_not_avoidsCenters (isNoetherian_ambientLevel_ofAffine A hemb hsnc hsm k Y pY) hopen hcent i (le_of_lt hi) (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι …`. Use `show ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).detachedToBase i).base q ∈ ((smoothLocusComplement pY : TopologicalSpace.Closeds ↥Y) : Set ↥Y)`. Rewrite using `[AffineSpacePrincipalizationData.detachedToBase_def, base_comp_apply]`. Conclude with `hsing`.
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

/- English proof (translation)
Introduce `i hi`. Use `Set.Subset.antisymm ?_ (boundary_preimage_subset_smoothLocusComplement_preimage A hemb hsnc hsm k Y pY hopen hcent i hi)` and prove the remaining obligations. Introduce `q hq`. Assume the negation of the conclusion as `hcon`. Establish `hboundary : ∀ E ∈ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i, ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base q) ∉ …`.

Introduce `E hE hmem`. Use `hcon ?_` and prove the remaining obligations. Establish `hb` using `base_comp_apply ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i) ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i) q`. Simplify using `only [Set.mem_preimage, hb]`. Conclude with `Set.mem_iUnion₂.mpr ⟨E, hE, hmem⟩`.

Conclude with `(AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).notMem_smoothLocusComplement_detachedToBase_of_notMem_boundary (isNoetherian_ambientLevel_ofAffine A hemb hsnc hsm k Y pY) hopen hsmooth i hi q hboundary hq`.
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

/- English proof (translation)
Introduce `k _ _ Y pY _ _ _ _`. Use `detachedSingularPreimageEqBoundary_ofAffine A hemb hsnc hsm k Y pY (hiso k Y pY) (hsmooth k Y pY) ?_` and prove the remaining obligations. Conclude with `AffineSpacePrincipalizationData.centersLieOverSingularLocus_of_inducedCentersLieOverSingularLocus (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) (hPrincipalization k Y pY) (hcent k Y pY)`.
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
