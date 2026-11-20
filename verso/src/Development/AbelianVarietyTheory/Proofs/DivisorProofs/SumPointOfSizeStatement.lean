import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfSize
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSumPointOfSize.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.sum_point_of_size : Size → SumPt := by
  first | exact @GlobalTheory.RefSum.sumPt_of_size | exact GlobalTheory.RefSum.sumPt_of_size | (intros; apply GlobalTheory.RefSum.sumPt_of_size <;> assumption)
