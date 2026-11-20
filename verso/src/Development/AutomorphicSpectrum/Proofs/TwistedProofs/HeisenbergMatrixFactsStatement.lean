import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.HeisenbergMatrixFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FHeisenbergMatrixFacts.lean&line=353#L353)
-/
theorem _root_.GlobalTheory.T.heisenberg_matrix_facts : Heis := by
  first | exact @GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ | exact GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ | (intros; apply GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ <;> assumption)
