import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuationAlt
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.abel_continuation : AbelContinuation := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation <;> assumption)
