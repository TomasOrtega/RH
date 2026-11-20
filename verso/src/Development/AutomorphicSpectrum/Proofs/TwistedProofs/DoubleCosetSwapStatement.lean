import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.DoubleCosetSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FDoubleCosetSwap.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.double_coset_swap : DosetSwap := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.dosetSwap | exact GlobalTheory.CompanionTheory.InertZeta.dosetSwap | (intros; apply GlobalTheory.CompanionTheory.InertZeta.dosetSwap <;> assumption)
