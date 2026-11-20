import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosetsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodularStatement

open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ H _ _ hH hG hH' dg _ ν _`. Take `⟨⟨μ₀, hμ₀⟩, huniq⟩` from `GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular G H hH hG hH'`. Take `⟨dg₀, ⟨hdg₀, hF₀⟩, -⟩` from `GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ₀ hμ₀`. Use `set c : ℝ≥0 := haarScalarFactor dg dg₀ with hc`. Establish `hcpos : 0 < c` using `haarScalarFactor_pos_of_isHaarMeasure dg dg₀`.

Establish `hdg : dg = c • dg₀` using `isMulLeftInvariant_eq_smul dg dg₀`. Establish `hR : IsInvariantRadon H (c • μ₀)` using `by haveI := hμ₀.finiteOnCompacts haveI := hμ₀.invariant`. Use `⟨?_, inferInstance, ⟨fun g s hs => ?_⟩⟩` and prove the remaining obligations. Introduce `h`. Apply `hμ₀.ne_zero` to reduce the goal to its premises.

Establish `: c⁻¹ • (c • μ₀) = μ₀`. Rewrite using `[smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]`. Rewrite using `[← this, h, smul_zero]`. Simplify using `only [Measure.coe_nnreal_smul_apply]`. Rewrite using `[SMulInvariantMeasure.measure_preimage_smul g hs]`.

Establish `hF : QuotientFormula H dg ν (c • μ₀)`. Introduce `f hf`. Take `⟨h1, h2⟩` from `hF₀ f hf`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[hdg, lintegral_smul_measure, lintegral_smul_measure, h2]`.

Use `⟨c • μ₀, ⟨hR, hF⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `μ ⟨hμ, hμF⟩`. Take `⟨d, -, hd⟩` from `huniq _ _ hR hμ`. Take `⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G)` from `inferInstance`. Establish `hKm : MeasurableSet (K : Set G)` using `K.isCompact.measurableSet`.

Establish `hfm : Measurable ((K : Set G).indicator (fun _ => (1 : ℝ≥0∞)))` using `measurable_const.indicator hKm`. Establish `e1` using `(hF _ hfm).2`. Establish `e2` using `(hμF _ hfm).2`. Rewrite `e2` using `[hd, lintegral_smul_measure, ← e1, lintegral_indicator_const hKm, one_mul]`. Establish `hpos : dg K ≠ 0` using `(measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'`.

Establish `hfin : dg K ≠ ∞` using `K.isCompact.measure_lt_top.ne`. Establish `hd1 : d = 1`. Establish `: (d : ℝ≥0∞) * dg K = 1 * dg K`. Rewrite using `[one_mul]`. Conclude with `e2.symm`.

Conclude with `(ENNReal.mul_left_inj hpos hfin).mp this` after adjusting the coercions. Rewrite using `[hd, hd1, one_smul]`.
-/
theorem normaliseQuotientClause : NormaliseQuotientClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH hG hH' dg _ ν _
  obtain ⟨⟨μ₀, hμ₀⟩, huniq⟩ := GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular G H hH hG hH'
  obtain ⟨dg₀, ⟨hdg₀, hF₀⟩, -⟩ := GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ₀ hμ₀
  set c : ℝ≥0 := haarScalarFactor dg dg₀ with hc
  have hcpos : 0 < c := haarScalarFactor_pos_of_isHaarMeasure dg dg₀
  have hdg : dg = c • dg₀ := isMulLeftInvariant_eq_smul dg dg₀
  have hR : IsInvariantRadon H (c • μ₀) := by
    haveI := hμ₀.finiteOnCompacts
    haveI := hμ₀.invariant
    refine ⟨?_, inferInstance, ⟨fun g s hs => ?_⟩⟩
    · intro h
      apply hμ₀.ne_zero
      have : c⁻¹ • (c • μ₀) = μ₀ := by
        rw [smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
      rw [← this, h, smul_zero]
    · simp only [Measure.coe_nnreal_smul_apply]
      rw [SMulInvariantMeasure.measure_preimage_smul g hs]
  have hF : QuotientFormula H dg ν (c • μ₀) := by
    intro f hf
    obtain ⟨h1, h2⟩ := hF₀ f hf
    refine ⟨h1, ?_⟩
    rw [hdg, lintegral_smul_measure, lintegral_smul_measure, h2]
  refine ⟨c • μ₀, ⟨hR, hF⟩, ?_⟩
  rintro μ ⟨hμ, hμF⟩
  obtain ⟨d, -, hd⟩ := huniq _ _ hR hμ
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hKm : MeasurableSet (K : Set G) := K.isCompact.measurableSet
  have hfm : Measurable ((K : Set G).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hKm
  have e1 := (hF _ hfm).2
  have e2 := (hμF _ hfm).2
  rw [hd, lintegral_smul_measure, ← e1, lintegral_indicator_const hKm, one_mul] at e2
  have hpos : dg K ≠ 0 := (measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
  have hfin : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have hd1 : d = 1 := by
    have : (d : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]; exact e2.symm
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).mp this
  rw [hd, hd1, one_smul]

end GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique
