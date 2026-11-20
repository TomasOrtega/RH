import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetric
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ChernDegree.chernWeilNumbers_holds | exact GlobalTheory.ChernDegree.chernWeilNumbers_holds | (intros; apply GlobalTheory.ChernDegree.chernWeilNumbers_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric : GlobalTheory.Published.ChernWeilNumbers := by
  first | exact @GlobalTheory.ChernDegree.chernWeilNumbers_holds | exact GlobalTheory.ChernDegree.chernWeilNumbers_holds | (intros; apply GlobalTheory.ChernDegree.chernWeilNumbers_holds <;> assumption)
