import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPairingContinuousFunctional
import Mathlib
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzPairingContinuousFunctional.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.schwartz_pairing_continuous_functional : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (k : SchwartzMap V ℂ),
    ∃ L : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ, L u = ∫ x, u x * starRingEnd ℂ (k x) ∂μ := by
  first | exact @GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace | exact GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace | (intros; apply GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace <;> assumption)
