import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetSurjectiveOfLevi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InertCoset.cosetSurj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FCosetSurjectiveOfLevi.lean&line=711#L711)
-/
theorem _root_.GlobalTheory.T.coset_surjective_of_levi : LeviExists → CosetSurj := by
  first | exact @GlobalTheory.CompanionTheory.InertCoset.cosetSurj | exact GlobalTheory.CompanionTheory.InertCoset.cosetSurj | (intros; apply GlobalTheory.CompanionTheory.InertCoset.cosetSurj <;> assumption)
