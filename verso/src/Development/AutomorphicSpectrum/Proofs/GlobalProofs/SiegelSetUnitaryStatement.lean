import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FSiegelSetUnitary.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.siegel_set_unitary : GlobalTheory.Published.SiegelSetUnitary := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary | exact GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary | (intros; apply GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary <;> assumption)
