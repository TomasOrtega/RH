import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateCommutes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.left_translate_commutes : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob | exact GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob | (intros; apply GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob <;> assumption)
