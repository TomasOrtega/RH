import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary | exact GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary | (intros; apply GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.siegel_set_unitary : GlobalTheory.Published.SiegelSetUnitary := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary | exact GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary | (intros; apply GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary <;> assumption)
