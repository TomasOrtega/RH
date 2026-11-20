import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GLInvMulCongrOneModUniformizer
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GL_inv_mul_congr_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FGLInvMulCongrOneModUniformizer.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.GL_inv_mul_congr_one_mod_uniformizer : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {N : ℕ} (π : K), π ≠ 0 → Valued.v π < 1 →
  ∀ (a a₁ : GL (Fin N) K), (∀ i j, Valued.v (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    (∀ i j, Valued.v (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    ∀ i j, Valued.v (π⁻¹ * (((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1 := by
  first | exact @GlobalTheory.GL_inv_mul_congr_one | exact GlobalTheory.GL_inv_mul_congr_one | (intros; apply GlobalTheory.GL_inv_mul_congr_one <;> assumption)
