import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleRankOneLeft
import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralModuleRankOneLeft.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.integral_module_rank_one_left : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ v φ : Fin n → ℂ, φ ⬝ᵥ v = 1 → IsIntMod (invAlg ρ) (leftIdl ρ {Y | ∃ u, φ ⬝ᵥ u = 0 ∧ Y = vecMulVec u φ}) (ρ (vecMulVec v φ)) := by
  first | exact @GlobalTheory.rho_vecMulVec_isIntMod_invAlg | exact GlobalTheory.rho_vecMulVec_isIntMod_invAlg | (intros; apply GlobalTheory.rho_vecMulVec_isIntMod_invAlg <;> assumption)
