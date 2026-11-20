import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticRiemannRochAbelianOfQuoted
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbelianRR.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithmeticRiemannRochAbelianOfQuoted.lean&line=193#L193)
-/
theorem _root_.GlobalTheory.T.arithmetic_riemann_roch_abelian_of_quoted : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch → GlobalTheory.Published.ArithRiemannRochAbelian := by
  first | exact @GlobalTheory.AbelianRR.main | exact GlobalTheory.AbelianRR.main | (intros; apply GlobalTheory.AbelianRR.main <;> assumption)
