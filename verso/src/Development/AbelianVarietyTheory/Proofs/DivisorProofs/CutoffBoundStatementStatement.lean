import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffBoundStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTop.cut_of_hypotheses` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCutoffBoundStatement.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.cutoff_bound_statement : Hypotheses2 → Cut := by
  first | exact @GlobalTheory.CovTop.cut_of_hypotheses | exact GlobalTheory.CovTop.cut_of_hypotheses | (intros; apply GlobalTheory.CovTop.cut_of_hypotheses <;> assumption)
