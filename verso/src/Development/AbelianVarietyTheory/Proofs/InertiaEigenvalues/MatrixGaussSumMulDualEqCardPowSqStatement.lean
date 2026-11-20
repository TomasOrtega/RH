import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumMulDualEqCardPowSq
open Matrix Finset
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMatrixGaussSumMulDualEqCardPowSq.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.matrixGaussSum_mul_dual_eq_card_pow_sq : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) * (∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ⁻¹ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) = (Fintype.card k : R) ^ (r ^ 2) := by
  first | exact @GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow | exact GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow | (intros; apply GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow <;> assumption)
