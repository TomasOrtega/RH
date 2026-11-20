import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSizeBoundStatement.lean&line=367#L367)
-/
theorem _root_.GlobalTheory.T.size_bound_statement : Size := by
  first | exact @GlobalTheory.CovTop.SizeRows.size | exact GlobalTheory.CovTop.SizeRows.size | (intros; apply GlobalTheory.CovTop.SizeRows.size <;> assumption)
