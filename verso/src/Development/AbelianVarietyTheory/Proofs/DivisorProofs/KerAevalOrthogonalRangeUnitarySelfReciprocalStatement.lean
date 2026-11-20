import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalOrthogonalRangeUnitarySelfReciprocal
import Mathlib
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.csr_ker_orth_range` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKerAevalOrthogonalRangeUnitarySelfReciprocal.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.ker_aeval_orthogonal_range_unitary_selfReciprocal : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K), (γ.map σ)ᵀ * γ = 1 → ∀ (Q : K[X]), C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse → ∀ (x z : Fin n → K), aeval γ Q *ᵥ x = 0 → ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 := by
  first | exact @GlobalTheory.csr_ker_orth_range | exact GlobalTheory.csr_ker_orth_range | (intros; apply GlobalTheory.csr_ker_orth_range <;> assumption)
