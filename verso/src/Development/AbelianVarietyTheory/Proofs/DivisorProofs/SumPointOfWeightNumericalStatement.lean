import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfWeightNumerical
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RefSum.sumPt_of_sizes` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSumPointOfWeightNumerical.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.sum_point_of_weight_numerical : WtPt → NumPt → SumPt := by
  first | exact @GlobalTheory.RefSum.sumPt_of_sizes | exact GlobalTheory.RefSum.sumPt_of_sizes | (intros; apply GlobalTheory.RefSum.sumPt_of_sizes <;> assumption)
