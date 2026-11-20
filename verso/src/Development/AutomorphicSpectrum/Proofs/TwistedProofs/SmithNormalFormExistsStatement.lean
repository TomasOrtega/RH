import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmithNormalFormExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InertSmith.smith` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FSmithNormalFormExists.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.smith_normal_form_exists : Smith := by
  first | exact @GlobalTheory.CompanionTheory.InertSmith.smith | exact GlobalTheory.CompanionTheory.InertSmith.smith | (intros; apply GlobalTheory.CompanionTheory.InertSmith.smith <;> assumption)
