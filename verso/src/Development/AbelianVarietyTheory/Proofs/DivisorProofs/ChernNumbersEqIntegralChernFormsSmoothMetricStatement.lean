import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetric
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChernDegree.chernWeilNumbers_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChernNumbersEqIntegralChernFormsSmoothMetric.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric : GlobalTheory.Published.ChernWeilNumbers := by
  first | exact @GlobalTheory.ChernDegree.chernWeilNumbers_holds | exact GlobalTheory.ChernDegree.chernWeilNumbers_holds | (intros; apply GlobalTheory.ChernDegree.chernWeilNumbers_holds <;> assumption)
