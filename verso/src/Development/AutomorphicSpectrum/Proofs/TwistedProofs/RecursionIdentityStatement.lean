import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.RecursionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InertLevi.step` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FRecursionIdentity.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.recursion_identity : Step := by
  first | exact @GlobalTheory.CompanionTheory.InertLevi.step | exact GlobalTheory.CompanionTheory.InertLevi.step | (intros; apply GlobalTheory.CompanionTheory.InertLevi.step <;> assumption)
