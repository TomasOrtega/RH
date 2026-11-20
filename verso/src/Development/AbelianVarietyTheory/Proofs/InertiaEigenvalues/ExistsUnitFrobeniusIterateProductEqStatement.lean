import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitFrobeniusIterateProductEq
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsUnitFrobeniusIterateProductEq.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.exists_unit_frobenius_iterate_product_eq : ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A → ∀ (φ : A →+* A) (u : A), IsUnit u → (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) → ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  first | exact @GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | exact GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | (intros; apply GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq <;> assumption)
