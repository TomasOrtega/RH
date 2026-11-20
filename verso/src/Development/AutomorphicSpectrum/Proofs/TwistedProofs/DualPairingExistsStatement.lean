import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.DualPairingExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InertDual.dual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FDualPairingExists.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.dual_pairing_exists : Dual := by
  first | exact @GlobalTheory.CompanionTheory.InertDual.dual | exact GlobalTheory.CompanionTheory.InertDual.dual | (intros; apply GlobalTheory.CompanionTheory.InertDual.dual <;> assumption)
