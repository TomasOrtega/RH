import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergMeromorphicContinuation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRankinSelbergMeromorphicContinuation.lean&line=392#L392)
-/
theorem _root_.GlobalTheory.T.rankin_selberg_meromorphic_continuation : Ad3.Loc2 → Ad3.R.A10 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.a10 | exact GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.a10 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.a10 <;> assumption)
