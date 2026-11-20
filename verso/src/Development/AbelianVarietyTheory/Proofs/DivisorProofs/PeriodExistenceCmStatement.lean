import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodExistenceCm
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LatVal.periodEx_of_mainTheorem | exact GlobalTheory.LatVal.periodEx_of_mainTheorem | (intros; apply GlobalTheory.LatVal.periodEx_of_mainTheorem <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.period_existence_cm : GlobalTheory.Published.EllipticMainTheoremCM → PeriodEx := by
  first | exact @GlobalTheory.LatVal.periodEx_of_mainTheorem | exact GlobalTheory.LatVal.periodEx_of_mainTheorem | (intros; apply GlobalTheory.LatVal.periodEx_of_mainTheorem <;> assumption)
