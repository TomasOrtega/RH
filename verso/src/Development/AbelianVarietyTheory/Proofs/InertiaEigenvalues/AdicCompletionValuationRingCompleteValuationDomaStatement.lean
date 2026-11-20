import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDoma
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.adicCompletion_valuationRing_props` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdicCompletionValuationRingCompleteValuationDoma.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.adicCompletion_valuationRing_complete_valuationDomain : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : V), x ≠ 0 → ¬ IsUnit x → IsDomain (AdicCompletion (Ideal.span {x}) V) ∧ PreValuationRing (AdicCompletion (Ideal.span {x}) V) ∧ algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 ∧ ¬ IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ∧ IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}) (AdicCompletion (Ideal.span {x}) V) := by
  first | exact @GlobalTheory.adicCompletion_valuationRing_props | exact GlobalTheory.adicCompletion_valuationRing_props | (intros; apply GlobalTheory.adicCompletion_valuationRing_props <;> assumption)
