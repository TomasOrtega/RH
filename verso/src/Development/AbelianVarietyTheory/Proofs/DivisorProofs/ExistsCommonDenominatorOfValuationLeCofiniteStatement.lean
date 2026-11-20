import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorOfValuationLeCofinite
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCommonDenominatorOfValuationLeCofinite.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite : ∀ (E : Type) [Field E] [NumberField E] (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)),
    (∀ᶠ w in Filter.cofinite, β w ≤ 1) → ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) → IsIntegral ℤ ((D : E) * x) := by
  first | exact @GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le | exact GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le | (intros; apply GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le <;> assumption)
