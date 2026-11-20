import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.FractionExistsOfSmith
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FFractionExistsOfSmith.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.fraction_exists_of_smith : Smith → FracExists := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith | exact GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith | (intros; apply GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith <;> assumption)
