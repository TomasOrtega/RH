import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImply
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTop.Hypotheses2.toClassicalTheorems` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStrongerPublishedHypothesesImply.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.stronger_published_hypotheses_imply : Hypotheses2 → Hypotheses₂ := by
  first | exact @GlobalTheory.CovTop.Hypotheses2.toClassicalTheorems | exact GlobalTheory.CovTop.Hypotheses2.toClassicalTheorems | (intros; apply GlobalTheory.CovTop.Hypotheses2.toClassicalTheorems <;> assumption)
