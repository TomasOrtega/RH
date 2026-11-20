import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefficientCongruenceOfTwistedValues
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.CoefVal.coeff_cg_of_values` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCoefficientCongruenceOfTwistedValues.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.coefficient_congruence_of_twisted_values : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (k m₁ : ℕ), (∀ n, F.coeff n ∈ c.O) → (∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) → ∀ n, Cg k (F.coeff n) 0 := by
  first | exact @GlobalTheory.KZ.CoefVal.coeff_cg_of_values | exact GlobalTheory.KZ.CoefVal.coeff_cg_of_values | (intros; apply GlobalTheory.KZ.CoefVal.coeff_cg_of_values <;> assumption)
