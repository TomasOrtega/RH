import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.AdditiveVectorExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FAdditiveVectorExists.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.additive_vector_exists : AddVec := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.addVec | exact GlobalTheory.CompanionTheory.InertZeta.addVec | (intros; apply GlobalTheory.CompanionTheory.InertZeta.addVec <;> assumption)
