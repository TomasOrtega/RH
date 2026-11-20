import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Rewrite `h`, the goal using `[inStrictNormalCrossingPosition_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `D hD`. Rewrite `hD` using `[List.mem_map]`. Take `⟨D', hD', rfl⟩` from `hD`.

Conclude with `PrincipalizationIsoTransport.isSmoothDivisor_comap_iso q e D' (h.1 D' hD')`. Introduce `x`. Take `⟨U, hxU, m, c, a, hinj, hnone, hsome⟩` from `h.2 (e.hom.base x)`. Use `⟨(TopologicalSpace.Opens.map e.hom.base).obj U, hxU, m, EtaleChart.ofIso q e c, a, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi j hj t hti htj`.

Conclude with `hinj i (by simpa using hi) j (by simpa using hj) t hti htj`. Introduce `i hi ha`. Establish `hi' : i < L.length` using `by simpa using hi`. Simplify using `only [List.getElem_map]`. Rewrite using `[restrictIdeal_comap, hnone i hi' ha, Scheme.IdealSheafData.comap_top]`.

Introduce `i hi t ht`. Establish `hi' : i < L.length` using `by simpa using hi`. Simplify using `only [List.getElem_map]`. Rewrite using `[restrictIdeal_comap, hsome i hi' t ht, EtaleChart.ofIso_coordIdeal]`.
-/
theorem inStrictNormalCrossingPosition_comap_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (L : List Y.IdealSheafData)
    (h : InStrictNormalCrossingPosition q L) :
    InStrictNormalCrossingPosition (e.hom ≫ q) (L.map (fun D => D.comap e.hom)) := by
  rw [inStrictNormalCrossingPosition_iff] at h ⊢
  refine ⟨?_, ?_⟩
  · intro D hD
    rw [List.mem_map] at hD
    obtain ⟨D', hD', rfl⟩ := hD
    exact PrincipalizationIsoTransport.isSmoothDivisor_comap_iso q e D' (h.1 D' hD')
  · intro x
    obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := h.2 (e.hom.base x)
    refine ⟨(TopologicalSpace.Opens.map e.hom.base).obj U, hxU, m,
      EtaleChart.ofIso q e c, a, ?_, ?_, ?_⟩
    · intro i hi j hj t hti htj
      exact hinj i (by simpa using hi) j (by simpa using hj) t hti htj
    · intro i hi ha
      have hi' : i < L.length := by simpa using hi
      simp only [List.getElem_map]
      rw [restrictIdeal_comap, hnone i hi' ha, Scheme.IdealSheafData.comap_top]
    · intro i hi t ht
      have hi' : i < L.length := by simpa using hi
      simp only [List.getElem_map]
      rw [restrictIdeal_comap, hsome i hi' t ht, EtaleChart.ofIso_coordIdeal]

namespace MarkedSequenceOfBlowups

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

/- English proof (translation)
Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedSequenceOfBlowups.projectionToBase_zero]`.
-/
theorem projectionToSpec_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.projectionToSpec 0 = s.toSequenceOfBlowups.isoZero.hom ≫ p := by
  rw [MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedSequenceOfBlowups.projectionToBase_zero]

/- English proof (translation)
Establish `h : s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i = s.toSequenceOfBlowups.projectionToBase (i + 1)`. Rewrite using `[s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i]`. Conclude with `s.toSequenceOfBlowups.transitionMap_comp_projectionToBase (Nat.le_succ i)`. Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedSequenceOfBlowups.projectionToSpec_eq, ← h, Category.assoc]`.
-/
theorem projectionToSpec_succ (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.projectionToSpec (i + 1) = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.projectionToSpec i := by
  have h : s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i
      = s.toSequenceOfBlowups.projectionToBase (i + 1) := by
    rw [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i]
    exact s.toSequenceOfBlowups.transitionMap_comp_projectionToBase (Nat.le_succ i)
  rw [MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedSequenceOfBlowups.projectionToSpec_eq, ← h, Category.assoc]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero`. Establish `: AlgebraicGeometry.IsNoetherian T.scheme` using `hT.isNoetherian`. Conclude with `isNoetherian_of_iso s.toSequenceOfBlowups.isoZero.symm`. Consider the case `succ n ih`.

Establish `hn : n < s.toSequenceOfBlowups.length` using `hi`. Establish `: AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt n)` using `ih (le_of_lt hn)`. Conclude with `isNoetherian_of_isBlowupAlongIdealSheaf (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)`.
-/
theorem isNoetherian_schemeAt (_hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt i) := by
  induction i with
  | zero =>
      have : AlgebraicGeometry.IsNoetherian T.scheme := hT.isNoetherian
      exact isNoetherian_of_iso s.toSequenceOfBlowups.isoZero.symm
  | succ n ih =>
      have hn : n < s.toSequenceOfBlowups.length := hi
      have : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt n) := ih (le_of_lt hn)
      exact isNoetherian_of_isBlowupAlongIdealSheaf (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

end MarkedSequenceOfBlowups

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_`. Establish `: AlgebraicGeometry.Smooth T.structMap` using `hT.smooth`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_zero] infer_instance`. Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_zero, s.boundary_zero]`. Conclude with `inStrictNormalCrossingPosition_comap_iso T.structMap s.toSequenceOfBlowups.isoZero T.boundary hT.snc`. Consider the case `succ n ih`.

Introduce `hn`. Establish `hn' : n < s.toSequenceOfBlowups.length` using `hn`. Take `⟨hsm, hsnc⟩` from `ih (le_of_lt hn')`. Establish `: AlgebraicGeometry.Smooth (s.projectionToSpec n)` using `hsm`. Establish `: AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (n + 1))` using `MarkedSequenceOfBlowups.isNoetherian_schemeAt hcart hT s (n + 1) hn`.

Establish `: TopologicalSpace.NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt (n + 1))` using `inferInstance`. Establish `hπ` using `s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn'`. Establish `hZE : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.toSequenceOfBlowups.center n) (s.boundary n)`. Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_eq]`. Conclude with `s.center_snc n hn'`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_succ]`. Conclude with `smooth_comp_of_isBlowupAlongIdealSheaf hZE hπ`. Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_succ, s.boundary_succ n hn']`. Conclude with `inStrictNormalCrossingPosition_strictTransform_append (s.projectionToSpec n) (s.toSequenceOfBlowups.transitionMapSucc n) (s.toSequenceOfBlowups.center n) (s.boundary n) hπ hsnc hZE`.
-/
private theorem smooth_and_inStrictNormalCrossingPosition_projectionToSpec (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) :
    ∀ i : ℕ, i ≤ s.toSequenceOfBlowups.length →
      AlgebraicGeometry.Smooth (s.projectionToSpec i) ∧ InStrictNormalCrossingPosition (s.projectionToSpec i) (s.boundary i) := by
  intro i
  induction i with
  | zero =>
      intro _
      have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
      refine ⟨?_, ?_⟩
      · rw [MarkedSequenceOfBlowups.projectionToSpec_zero]
        infer_instance
      · rw [MarkedSequenceOfBlowups.projectionToSpec_zero, s.boundary_zero]
        exact inStrictNormalCrossingPosition_comap_iso T.structMap s.toSequenceOfBlowups.isoZero T.boundary hT.snc
  | succ n ih =>
      intro hn
      have hn' : n < s.toSequenceOfBlowups.length := hn
      obtain ⟨hsm, hsnc⟩ := ih (le_of_lt hn')
      have : AlgebraicGeometry.Smooth (s.projectionToSpec n) := hsm
      have : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (n + 1)) :=
        MarkedSequenceOfBlowups.isNoetherian_schemeAt hcart hT s (n + 1) hn
      have : TopologicalSpace.NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt (n + 1)) := inferInstance
      have hπ := s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn'
      have hZE : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.toSequenceOfBlowups.center n) (s.boundary n) := by
        rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
        exact s.center_snc n hn'
      refine ⟨?_, ?_⟩
      · rw [MarkedSequenceOfBlowups.projectionToSpec_succ]
        exact smooth_comp_of_isBlowupAlongIdealSheaf hZE hπ
      · rw [MarkedSequenceOfBlowups.projectionToSpec_succ, s.boundary_succ n hn']
        exact inStrictNormalCrossingPosition_strictTransform_append (s.projectionToSpec n) (s.toSequenceOfBlowups.transitionMapSucc n)
          (s.toSequenceOfBlowups.center n) (s.boundary n) hπ hsnc hZE

namespace MarkedSequenceOfBlowups

/- English proof (translation)
The claim follows from `(smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi).1`.
-/
theorem smooth_projectionToSpec (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.Smooth (s.projectionToSpec i) :=
  (smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi).1

/- English proof (translation)
The claim follows from `(smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi).2`.
-/
theorem inStrictNormalCrossingPosition_projectionToSpec_boundary (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    InStrictNormalCrossingPosition (s.projectionToSpec i) (s.boundary i) :=
  (smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi).2

end MarkedSequenceOfBlowups

def DimensionNonincreasingAlongBlowups : Prop :=
  ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
    krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc

namespace MarkedIdealWithBoundary

def transformAt (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := s.toSequenceOfBlowups.schemeAt i
  structMap := s.projectionToSpec i
  ideal := s.ideal i
  mult := T.mult
  boundary := s.boundary i

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem transformAt_baseField (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).base = T.base := rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem transformAt_scheme (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).scheme = s.toSequenceOfBlowups.schemeAt i := rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem transformAt_structureMorphism (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).structMap = s.projectionToSpec i := rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem transformAt_ideal (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).ideal = s.ideal i := rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem transformAt_mult (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).mult = T.mult := rfl

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem transformAt_boundary (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).boundary = s.boundary i := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem transformAt_dim (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).krullDimSucc = EmbeddedResolution.krullDimSucc (s.toSequenceOfBlowups.schemeAt i) := rfl

/- English proof (translation)
Take `⟨hsm, hsnc⟩` from `smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi`. Establish `: AlgebraicGeometry.Smooth (s.projectionToSpec i)` using `hsm`. Establish `: AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt i)` using `MarkedSequenceOfBlowups.isNoetherian_schemeAt hcart hT s i hi`. Establish `: TopologicalSpace.NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt i)` using `inferInstance`. Use `{ charZero := hT.charZero locallyOfFiniteType := ?_ nonzeroOnComponents := MarkedSequenceOfBlowups.nonzeroOnComponents_ideal_of_isAdmissible hcart hT s i hi one_le_mult := hT.one_le_mult quasiCompact := ?_ smooth := hsm snc := hsnc }` and prove the remaining obligations.

Use `show AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec i) infer_instance`. Use `show AlgebraicGeometry.QuasiCompact (s.projectionToSpec i)`. Conclude with `⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩`.
-/
theorem IsAdmissible.transformAt (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    (T.transformAt s i).IsAdmissible := by
  obtain ⟨hsm, hsnc⟩ := smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi
  have : AlgebraicGeometry.Smooth (s.projectionToSpec i) := hsm
  have : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt hcart hT s i hi
  have : TopologicalSpace.NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt i) := inferInstance
  refine
    { charZero := hT.charZero
      locallyOfFiniteType := ?_
      nonzeroOnComponents := MarkedSequenceOfBlowups.nonzeroOnComponents_ideal_of_isAdmissible hcart hT s i hi
      one_le_mult := hT.one_le_mult
      quasiCompact := ?_
      smooth := hsm
      snc := hsnc }
  · show AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec i)
    infer_instance
  · show AlgebraicGeometry.QuasiCompact (s.projectionToSpec i)
    exact ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩

/- English proof (translation)
The claim follows from `hdim T hT s i hi`.
-/
theorem transformAt_dim_le (hdim : DimensionNonincreasingAlongBlowups.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    (T.transformAt s i).krullDimSucc ≤ T.krullDimSucc :=
  hdim T hT s i hi

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution

end
