import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuationAlt
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FAbelContinuationAlt.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.abel_continuation : AbelContinuation := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation <;> assumption)
