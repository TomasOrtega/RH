import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDenominatorIntegral
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_unit_at_prime_mul_integral` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUnitDenominatorIntegral.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_unit_denominator_integral : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (T : Set K) (d : 𝓞 K), d ≠ 0 → (∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) → (∀ t ∈ T, P.valuation K t ≤ 1) → ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) := by
  first | exact @GlobalTheory.exists_unit_at_prime_mul_integral | exact GlobalTheory.exists_unit_at_prime_mul_integral | (intros; apply GlobalTheory.exists_unit_at_prime_mul_integral <;> assumption)
