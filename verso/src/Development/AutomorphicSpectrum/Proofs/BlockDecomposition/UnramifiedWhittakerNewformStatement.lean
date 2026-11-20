import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedWhittakerNewform.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.unramified_whittaker_newform : Ad3.R.U2 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | exact GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char <;> assumption)
