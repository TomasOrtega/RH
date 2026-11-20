import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivExtendingOfKerLe
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_ringEquiv_extending_of_ker_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsRingEquivExtendingOfKerLe.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_ringEquiv_extending_of_ker_le' : ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) → ∀ (R : Subring k) (J : Type) (α β : J → k), (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) → ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by
  first | exact @GlobalTheory.exists_ringEquiv_extending_of_ker_le | exact GlobalTheory.exists_ringEquiv_extending_of_ker_le | (intros; apply GlobalTheory.exists_ringEquiv_extending_of_ker_le <;> assumption)
