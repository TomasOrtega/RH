import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianMulAddDetNeZeroOfPair
import Mathlib
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSkewHermitianMulAddDetNeZeroOfPair.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  first | exact @GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair | exact GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair | (intros; apply GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair <;> assumption)
