import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallCornerOfHeisenbergDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FSmallCornerOfHeisenbergDual.lean&line=166#L166)
-/
theorem _root_.GlobalTheory.T.small_corner_of_heisenberg_dual : Heis → Dual → SmallCorner := by
  first | exact @GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis | exact GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis | (intros; apply GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis <;> assumption)
