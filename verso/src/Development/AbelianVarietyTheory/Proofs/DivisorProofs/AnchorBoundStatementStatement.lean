import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAnchorBoundStatement.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.anchor_bound_statement : Anchor := by
  first | exact @GlobalTheory.CovTop.anchor_holds | exact GlobalTheory.CovTop.anchor_holds | (intros; apply GlobalTheory.CovTop.anchor_holds <;> assumption)
