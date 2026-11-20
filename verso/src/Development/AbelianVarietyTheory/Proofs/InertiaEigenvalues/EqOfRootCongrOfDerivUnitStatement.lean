import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnit
import Mathlib
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.eq_of_root_congr_of_deriv_unit` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEqOfRootCongrOfDerivUnit.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.eq_of_roots_congr_of_derivative_unit : ∀ {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Polynomial ℤ) (β β' : Ω),
    A.valuation β ≤ 1 → A.valuation β' ≤ 1 → Polynomial.aeval β f = 0 → Polynomial.aeval β' f = 0 →
    ¬ A.valuation (Polynomial.aeval β (Polynomial.derivative f)) < 1 → A.valuation (β - β') < 1 → β = β' := by
  first | exact @GlobalTheory.eq_of_root_congr_of_deriv_unit | exact GlobalTheory.eq_of_root_congr_of_deriv_unit | (intros; apply GlobalTheory.eq_of_root_congr_of_deriv_unit <;> assumption)
