import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.LeviDecompositionExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FLeviDecompositionExists.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.levi_decomposition_exists : LeviExists := by
  first | exact @GlobalTheory.CompanionTheory.InertLevi.leviExists | exact GlobalTheory.CompanionTheory.InertLevi.leviExists | (intros; apply GlobalTheory.CompanionTheory.InertLevi.leviExists <;> assumption)
