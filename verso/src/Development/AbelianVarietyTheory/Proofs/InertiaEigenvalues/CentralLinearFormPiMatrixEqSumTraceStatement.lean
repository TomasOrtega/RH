import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralLinearFormPiMatrixEqSumTrace
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCentralLinearFormPiMatrixEqSumTrace.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix : ∀ (k : Type) [Field k] (N : ℕ) (n : Fin N → ℕ) (τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k), (∀ x y, τ (x * y) = τ (y * x)) → ∃ c : Fin N → k, ∀ x, τ x = ∑ i, c i * (x i).trace := by
  first | exact @GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace | exact GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace | (intros; apply GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace <;> assumption)
