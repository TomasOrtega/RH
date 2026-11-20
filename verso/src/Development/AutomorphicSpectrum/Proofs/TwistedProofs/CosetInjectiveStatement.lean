import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetInj | exact GlobalTheory.CompanionTheory.InertZeta.cosetInj | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetInj <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.coset_injective : CosetInj := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetInj | exact GlobalTheory.CompanionTheory.InertZeta.cosetInj | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetInj <;> assumption)
