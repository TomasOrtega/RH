import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticRiemannRochAbelianQuoted
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.arithRiemannRochAbelian_of_knownResults_known` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithmeticRiemannRochAbelianQuoted.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.arithmetic_riemann_roch_abelian_quoted : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch → GlobalTheory.Published.ArithRiemannRochAbelian := by
  first | exact @GlobalTheory.arithRiemannRochAbelian_of_knownResults_known | exact GlobalTheory.arithRiemannRochAbelian_of_knownResults_known | (intros; apply GlobalTheory.arithRiemannRochAbelian_of_knownResults_known <;> assumption)
