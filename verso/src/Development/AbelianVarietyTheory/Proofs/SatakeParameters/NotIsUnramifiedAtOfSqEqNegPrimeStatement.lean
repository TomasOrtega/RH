import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsUnramifiedAtOfSqEqNegPrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotSqMulUnit
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FNotIsUnramifiedAtOfSqEqNegPrime.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.not_isUnramifiedAt_of_sq_eq_neg_prime : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  first | exact @GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg | exact GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg | (intros; apply GlobalTheory.SqrtNegRam.not_isUnramifiedAt_of_sq_eq_neg <;> assumption)
