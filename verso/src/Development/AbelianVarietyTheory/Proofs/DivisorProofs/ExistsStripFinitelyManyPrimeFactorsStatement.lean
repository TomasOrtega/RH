import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStripFinitelyManyPrimeFactors
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsStripFinitelyManyPrimeFactors.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.exists_strip_finitely_many_prime_factors : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (x : R), x ≠ 0 → ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧ ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y := by
  first | exact @GlobalTheory.strip_prime_factors_target | exact GlobalTheory.strip_prime_factors_target | (intros; apply GlobalTheory.strip_prime_factors_target <;> assumption)
