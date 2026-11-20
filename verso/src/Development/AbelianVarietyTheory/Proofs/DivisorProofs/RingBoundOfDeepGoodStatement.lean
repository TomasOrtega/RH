import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingBoundOfDeepGood
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRingBoundOfDeepGood.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.ring_bound_of_deep_good : Hypotheses2 → Gram → DeepGood → Ring := by
  first | exact @GlobalTheory.CovTop.RingStep.ring_of | exact GlobalTheory.CovTop.RingStep.ring_of | (intros; apply GlobalTheory.CovTop.RingStep.ring_of <;> assumption)
