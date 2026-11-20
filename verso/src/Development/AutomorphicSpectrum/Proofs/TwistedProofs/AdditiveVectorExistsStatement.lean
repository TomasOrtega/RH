import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.AdditiveVectorExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.InertZeta.addVec | exact GlobalTheory.CompanionTheory.InertZeta.addVec | (intros; apply GlobalTheory.CompanionTheory.InertZeta.addVec <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.additive_vector_exists : AddVec := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.addVec | exact GlobalTheory.CompanionTheory.InertZeta.addVec | (intros; apply GlobalTheory.CompanionTheory.InertZeta.addVec <;> assumption)
