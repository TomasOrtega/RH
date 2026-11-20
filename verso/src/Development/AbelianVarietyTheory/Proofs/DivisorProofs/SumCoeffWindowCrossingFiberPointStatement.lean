import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCoeffWindowCrossingFiberPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagCurveCore.sum_coeff_fibPt` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSumCoeffWindowCrossingFiberPoint.lean&line=327#L327)
-/
theorem _root_.GlobalTheory.T.sum_coeff_window_crossing_fiber_point : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ), 1 ≤ j → j < N → ∑ p ∈ winSet ι N j, ∑ q ∈ crSet ι N j, coeff (mono (insert q ((winSet ι N j).erase p))) (toForm (fibPt ι N j) : FormPol ι N) = (Fintype.card ι : ℝ) * (2 * (j : ℝ) - N) * coeff (mono (winSet ι N j)) (toForm (fibPt ι N j) : FormPol ι N) := by
  first | exact @GlobalTheory.FlagCurveCore.sum_coeff_fibPt | exact GlobalTheory.FlagCurveCore.sum_coeff_fibPt | (intros; apply GlobalTheory.FlagCurveCore.sum_coeff_fibPt <;> assumption)
