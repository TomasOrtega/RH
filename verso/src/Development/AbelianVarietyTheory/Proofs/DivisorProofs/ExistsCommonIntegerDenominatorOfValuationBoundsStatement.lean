import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIntegerDenominatorOfValuationBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_nat_mul_integral_of_valuation_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCommonIntegerDenominatorOfValuationBounds.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_common_integer_denominator_of_valuation_bounds : ∀ (E : Type) [Field E] [NumberField E] (γ : Pl E → WithZero (Multiplicative ℤ)), (∀ᶠ u in cofinite, γ u ≤ 1) → ∃ d : ℕ, d ≠ 0 ∧ ∀ x : E, (∀ u : Pl E, u.valuation E x ≤ γ u) → ∃ a : 𝓞 E, (a : E) = d * x := by
  first | exact @GlobalTheory.exists_nat_mul_integral_of_valuation_le | exact GlobalTheory.exists_nat_mul_integral_of_valuation_le | (intros; apply GlobalTheory.exists_nat_mul_integral_of_valuation_le <;> assumption)
