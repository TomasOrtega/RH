import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotal
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FZeroCoefficientTotal.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.zero_coefficient_total : ZeroTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.zeroTotal | exact GlobalTheory.CompanionTheory.ThTot.zeroTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.zeroTotal <;> assumption)
