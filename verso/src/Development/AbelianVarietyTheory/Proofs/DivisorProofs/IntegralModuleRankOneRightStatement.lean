import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleRankOneRight
import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralModuleRankOneRight.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.integral_module_rank_one_right : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ v φ : Fin n → ℂ, φ ⬝ᵥ v = 1 → IsIntMod (invAlg ρ) (leftIdl ρ {Y | ∃ ψ, ψ ⬝ᵥ v = 0 ∧ Y = vecMulVec v ψ}) (ρ (vecMulVec v φ)) := by
  first | exact @GlobalTheory.TorFin.intMod_vecMulVec_row | exact GlobalTheory.TorFin.intMod_vecMulVec_row | (intros; apply GlobalTheory.TorFin.intMod_vecMulVec_row <;> assumption)
