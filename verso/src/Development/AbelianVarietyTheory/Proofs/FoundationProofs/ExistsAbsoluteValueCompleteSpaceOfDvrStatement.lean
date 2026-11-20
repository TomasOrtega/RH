import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvr
import Mathlib
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsAbsoluteValueCompleteSpaceOfDvr.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.exists_absoluteValue_completeSpace_of_dvr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K] [Algebra R K] [IsFractionRing R K], ∃ f : AbsoluteValue K ℝ, IsNonarchimedean f ∧ f.IsNontrivial ∧ (∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) ∧ CompleteSpace (WithAbs f) := by
  first | exact @GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing | exact GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing | (intros; apply GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing <;> assumption)
