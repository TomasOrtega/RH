import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExponentStrictlyLeastWeight
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsExponentStrictlyLeastWeight.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_least_weight_exponent : ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ, (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) → ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  first | exact @GlobalTheory.exists_exponent_strictly_least_weight | exact GlobalTheory.exists_exponent_strictly_least_weight | (intros; apply GlobalTheory.exists_exponent_strictly_least_weight <;> assumption)
