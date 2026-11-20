import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariantOnOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LogDerivIdealEstimate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariantSucc
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.RestrictedBlowupEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

namespace GoingUpInvariantOnOpen

/- English proof (translation)
Substitute `hL` using the available equality. Establish `h1 : i < (L.map f).length` using `by simpa using hi`. Rewrite using `[List.getElem_append_left h1, List.getElem_map]`.
-/
private theorem getElem_of_eq_map_append {α β : Type*} (f : α → β) (L : List α) (Lx : List β)
    (L' : List β) (hL : L' = L.map f ++ Lx) (i : ℕ) (hi : i < L.length) (hi' : i < L'.length) :
    L'[i]'hi' = f (L[i]'hi) := by
  subst hL
  have h1 : i < (L.map f).length := by simpa using hi
  rw [List.getElem_append_left h1, List.getElem_map]

/- English proof (translation)
Establish `hsmT : AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)` using `hinv.smooth_structMap`. Establish `hNt : AlgebraicGeometry.IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)` using `isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr t (by omega)`. Establish `hNt1 : AlgebraicGeometry.IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1))` using `isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (t + 1) (by omega)`. Establish `hNs1 : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (t + 1))` using `MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s (t + 1) (by omega)`. Establish `hNs : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt t)` using `MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s t (by omega)`.

Establish `hci : AlgebraicGeometry.IsClosedImmersion (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)` using `isClosedImmersion_restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ hU t`. Establish `hci1 : AlgebraicGeometry.IsClosedImmersion (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1))` using `isClosedImmersion_restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ hU (t + 1)`. Establish `htd : t < (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length`. Rewrite using `[ambientBlowupSeq_length]`. Conclude with `ht`.

Establish `hπ` using `(ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isBlowup t htd`. Establish `hHZ` using `ker_restrictedEmbedding_le_center hres hno T j hj I₀ E₀ s hpr U₀ hU hm hsupp t ht`. Establish `hsncC` using `hinv.hasStrictNormalCrossingsWith_center_cons hlift hm hV hU hsupp ht`. Establish `hsncZ` using `hinv.hasStrictNormalCrossingsWith_center hlift hm hV hU hsupp ht`. Establish `hsmT1 : AlgebraicGeometry.Smooth ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫ ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)` using `smooth_comp_of_isBlowupAlongIdealSheaf hsncC hπ`.

Establish `hps : ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1) = (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫ ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t` using `structureMorphism_ambientBlowupSeq_succ hres hno T j hj I₀ E₀ s hpr t`. Establish `hker1 : Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1)) = Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres h …` using `ker_restrictedEmbedding_succ T j hj I₀ E₀ s hres hno hpr U₀ hU t ht`. Establish `hidx : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).length`. Establish `h` using `hinv.idx_lt`. Rewrite `h`, the goal using `[BlowupSequenceData.boundary_length]`.

Use linear arithmetic over natural numbers and integers. Use `⟨?_, hidx, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl i hi`. Break down `lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h` into its components or cases. Conclude with `hinv.divDeriv l hl i h`.

Substitute `h` using the available equality. Conclude with `hinv.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift hU hsupp ht l hl`. Introduce `instFt n hn`. Establish `hest : ∀ m, m < T.mult → derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) m (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 t) ≤ ⨆ l, ⨆ _ : l ≤ m, logDerivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I …`. Introduce `m hmlt`.

Rewrite using `[ambientDerivIdeal_order_zero_eq_controlledTransform]`. Conclude with `hinv.deriv_le m hmlt`. Establish `hK : ∀ l, l ≤ T.mult → ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l)` using `fun l hl => hinv.ambientDerivIdeal_le_center_pow hbal hm hV hlift hU hsupp ht l hl`. Establish `hK' : ∀ l, l ≤ T.mult → Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ (T.mult - l) * ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1) = (ambientDerivIdeal hres hno T j hj I₀ E₀ s h …`. Introduce `l hl`.

Conclude with `BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ _ _ _ _ (hinv.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift hU hsupp ht l hl)`. Establish `hqc : AlgebraicGeometry.QuasiCompact (strictTransformι ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)))` using `FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian _ _ _`. Establish `key` using `derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) (Scheme.Hom.ker (restricte …`. Establish `e1 : derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) n ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1)) = derivIdealSheafIterate T.base ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map …` using `derivIdealSheafIterate_congr _ _ hps _ _`. Establish `e2 : ∀ l : ℕ, logDerivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1))) (n - l) (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) = logDerivIdealSh …`.

Introduce `l`. Rewrite using `[hker1]`. Conclude with `logDerivIdealSheafIterate_congr _ _ hps _ _ _`. Rewrite using `[e1]`. Simplify using `only [e2]`.

Establish `h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1) = ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 (t + 1)` using `(ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I₀ E₀ s hpr (t + 1)).symm`. Rewrite using `[h0]`. Conclude with `key`. Establish `hbs` using `BlowupSequenceData.boundary_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) E₀ t`. Establish `hlen : j < (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)).length`.

Simplify using `using hinv.idx_lt`. Establish `hZι : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) = (s.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι`. Rewrite using `[center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I₀ E₀ s hres hno hpr U₀ hU hm hsupp t ht]`. Conclude with `Blowup.comap_map_of_isClosedImmersion _ _`. Rewrite using `[hbs, List.eraseIdx_append_of_lt_length hlen _, List.eraseIdx_map, map_comap_strictTransform_append_exceptionalIdeal (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s …`.

Use `filterNeTop_map_append_congr _ ?_ _ _ _ hinv.comap_eraseIdx` and prove the remaining obligations. Conclude with `FunctorialResolution.EmbeddedResolution.strictTransform_top _ _`. Rewrite using `[hps, BlowupSequenceData.boundary_succ]`. Conclude with `inStrictNormalCrossingPosition_strictTransform_append _ _ _ _ hπ hinv.snc_bdry hsncZ`. Rewrite using `[hker1, ← hinv.bdry_getElem]`.

Conclude with `getElem_of_eq_map_append (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) [Blowup.exceptionalIdeal ((ambientBlowupSeq hres h …`. Rewrite using `[hps]`. Conclude with `hsmT1`.
-/
theorem succ {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (ht : t < s.length) :
    GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ (t + 1) := by
  have hsmT : AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hinv.smooth_structMap
  have hNt : AlgebraicGeometry.IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t) :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr t (by omega)
  have hNt1 : AlgebraicGeometry.IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (t + 1) (by omega)
  have hNs1 : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (t + 1)) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s (t + 1) (by omega)
  have hNs : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt t) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s t (by omega)
  have hci : AlgebraicGeometry.IsClosedImmersion
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) :=
    isClosedImmersion_restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ hU t
  have hci1 : AlgebraicGeometry.IsClosedImmersion
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1)) :=
    isClosedImmersion_restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ hU (t + 1)
  have htd : t < (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
    rw [ambientBlowupSeq_length]; exact ht
  have hπ := (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isBlowup t htd
  have hHZ := ker_restrictedEmbedding_le_center hres hno T j hj I₀ E₀ s hpr U₀ hU hm hsupp t ht
  have hsncC := hinv.hasStrictNormalCrossingsWith_center_cons hlift hm hV hU hsupp ht
  have hsncZ := hinv.hasStrictNormalCrossingsWith_center hlift hm hV hU hsupp ht
  have hsmT1 : AlgebraicGeometry.Smooth
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    smooth_comp_of_isBlowupAlongIdealSheaf hsncC hπ
  have hps : ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1) =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t :=
    structureMorphism_ambientBlowupSeq_succ hres hno T j hj I₀ E₀ s hpr t
  have hker1 : Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)) :=
    ker_restrictedEmbedding_succ T j hj I₀ E₀ s hres hno hpr U₀ hU t ht
  have hidx : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).length := by
    have h := hinv.idx_lt
    rw [BlowupSequenceData.boundary_length] at h ⊢
    omega
  refine ⟨?_, hidx, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl i hi
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
    · exact hinv.divDeriv l hl i h
    · subst h
      exact hinv.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift hU hsupp ht l hl
  · intro instFt n hn
    have hest : ∀ m, m < T.mult →
        derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) m
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 t) ≤
          ⨆ l, ⨆ _ : l ≤ m, logDerivIdealSheafIterate T.base
            (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
            (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)) (m - l)
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) := by
      intro m hmlt
      rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
      exact hinv.deriv_le m hmlt
    have hK : ∀ l, l ≤ T.mult →
        ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) := fun l hl =>
      hinv.ambientDerivIdeal_le_center_pow hbal hm hV hlift hU hsupp ht l hl
    have hK' : ∀ l, l ≤ T.mult →
        Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ (T.mult - l) *
            ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1) =
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := by
      intro l hl
      exact BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ _ _ _ _
        (hinv.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift hU hsupp ht l hl)
    have hqc : AlgebraicGeometry.QuasiCompact
        (strictTransformι ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
          (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))) :=
      FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian _ _ _
    have key := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup
      T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) hsncC hHZ hπ T.mult
      (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) hK hest
      (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) hK' n hn
    have e1 : derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1)) =
        derivIdealSheafIterate T.base
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1)) :=
      derivIdealSheafIterate_congr _ _ hps _ _
    have e2 : ∀ l : ℕ,
        logDerivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
            (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1))) (n - l)
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) =
          logDerivIdealSheafIterate T.base
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
              ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
            (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
              (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))) (n - l)
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) := by
      intro l
      rw [hker1]
      exact logDerivIdealSheafIterate_congr _ _ hps _ _ _
    rw [e1]
    simp only [e2]
    have h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1) =
        ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 (t + 1) :=
      (ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I₀ E₀ s hpr (t + 1)).symm
    rw [h0]
    exact key
  · have hbs := BlowupSequenceData.boundary_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) E₀ t
    have hlen : j < (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)).length := by
      simpa using hinv.idx_lt
    have hZι : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
        (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) =
        (s.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι := by
      rw [center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I₀ E₀ s hres hno hpr U₀ hU hm hsupp t ht]
      exact Blowup.comap_map_of_isClosedImmersion _ _
    rw [hbs, List.eraseIdx_append_of_lt_length hlen _, List.eraseIdx_map,
      map_comap_strictTransform_append_exceptionalIdeal (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)
        (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1))
        (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t)
        (restrictedEmbedding_comp_blowupMorphism T j hj I₀ E₀ s hres hno hpr U₀ t) hker1
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) hsncC hHZ hπ,
      boundary_comap_iteratedPreimage_succ T j hj I₀ E₀ s U₀ hV t ht, hZι]
    refine filterNeTop_map_append_congr _ ?_ _ _ _ hinv.comap_eraseIdx
    exact FunctorialResolution.EmbeddedResolution.strictTransform_top _ _
  · rw [hps, BlowupSequenceData.boundary_succ]
    exact inStrictNormalCrossingPosition_strictTransform_append _ _ _ _ hπ hinv.snc_bdry hsncZ
  · rw [hker1, ← hinv.bdry_getElem]
    exact getElem_of_eq_map_append
      (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)
      [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)]
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1))
      (BlowupSequenceData.boundary_succ _ E₀ t) j hinv.idx_lt hidx
  · rw [hps]
    exact hsmT1

end GoingUpInvariantOnOpen

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
