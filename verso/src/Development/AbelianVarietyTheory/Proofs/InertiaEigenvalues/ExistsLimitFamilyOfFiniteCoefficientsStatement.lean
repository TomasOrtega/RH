import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitFamilyOfFiniteCoefficients
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsLimitFamilyOfFiniteCoefficients.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_limit_family_of_finite_coefficients' : ∀ (σ I R : Type) [Finite σ] [Finite I] [Finite R] (F : ℕ → I → (σ →₀ ℕ) → R), ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧ ∀ x m, m.degree ≤ N → F M x m = G x m := by
  first | exact @GlobalTheory.exists_limit_family_of_finite_coefficients | exact GlobalTheory.exists_limit_family_of_finite_coefficients | (intros; apply GlobalTheory.exists_limit_family_of_finite_coefficients <;> assumption)
