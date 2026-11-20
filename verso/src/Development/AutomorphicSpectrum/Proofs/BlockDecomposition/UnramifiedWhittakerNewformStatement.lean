import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | exact GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unramified_whittaker_newform : Ad3.R.U2 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | exact GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char <;> assumption)
