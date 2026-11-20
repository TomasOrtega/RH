import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CompletionExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InertDoubling.completion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FCompletionExists.lean&line=205#L205)
-/
theorem _root_.GlobalTheory.T.completion_exists : Completion := by
  first | exact @GlobalTheory.CompanionTheory.InertDoubling.completion | exact GlobalTheory.CompanionTheory.InertDoubling.completion | (intros; apply GlobalTheory.CompanionTheory.InertDoubling.completion <;> assumption)
