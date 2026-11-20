import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirUnitaryGroupActsByScalarSmoothVectors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FCasimirUnitaryGroupActsByScalarSmoothVectors.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.casimir_unitaryGroup_acts_by_scalar_smoothVectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ χ : ℂ, ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v) := by
  first | exact @GlobalTheory.TypeSum.CasBasis.casimir_scalar | exact GlobalTheory.TypeSum.CasBasis.casimir_scalar | (intros; apply GlobalTheory.TypeSum.CasBasis.casimir_scalar <;> assumption)
