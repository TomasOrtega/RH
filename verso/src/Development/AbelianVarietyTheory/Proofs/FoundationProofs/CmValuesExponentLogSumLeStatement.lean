import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesExponentLogSumLe
import Formalism.PairingDivisors.StatementN
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.dividedPowerValuations_cESum | exact GlobalTheory.dividedPowerValuations_cESum | (intros; apply GlobalTheory.dividedPowerValuations_cESum <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cmValues_exponent_log_sum_le : Formalism.PairingDivisionLocalBalance.CESum := by
  first | exact @GlobalTheory.dividedPowerValuations_cESum | exact GlobalTheory.dividedPowerValuations_cESum | (intros; apply GlobalTheory.dividedPowerValuations_cESum <;> assumption)
