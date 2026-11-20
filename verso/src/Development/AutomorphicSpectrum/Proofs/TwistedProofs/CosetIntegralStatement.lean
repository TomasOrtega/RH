import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | exact GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetIntegral <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cosetIntegral' : CosetIntegral := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | exact GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetIntegral <;> assumption)
