import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateSobolev
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.KerFc.ltSob | exact GlobalTheory.CompanionTheory.KerFc.ltSob | (intros; apply GlobalTheory.CompanionTheory.KerFc.ltSob <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.left_translate_sobolev : GlobalTheory.CompanionTheory.KerFc.LtSob := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.ltSob | exact GlobalTheory.CompanionTheory.KerFc.ltSob | (intros; apply GlobalTheory.CompanionTheory.KerFc.ltSob <;> assumption)
