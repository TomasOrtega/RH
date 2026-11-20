import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodExistenceCm
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatVal.periodEx_of_mainTheorem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPeriodExistenceCm.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.period_existence_cm : GlobalTheory.Published.EllipticMainTheoremCM → PeriodEx := by
  first | exact @GlobalTheory.LatVal.periodEx_of_mainTheorem | exact GlobalTheory.LatVal.periodEx_of_mainTheorem | (intros; apply GlobalTheory.LatVal.periodEx_of_mainTheorem <;> assumption)
