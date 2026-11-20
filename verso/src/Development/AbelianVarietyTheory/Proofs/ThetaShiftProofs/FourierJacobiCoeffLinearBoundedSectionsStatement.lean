import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FourierJacobiCoeffLinearBoundedSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaShiftProofs%2FFourierJacobiCoeffLinearBoundedSections.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.fourierJacobi_coeff_linear_bounded_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (m : ℕ) (a : Fin m → ℂ) (Q : Fin m → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ), (∀ i, X.IsBddSec la (Q i)) → (∀ x ∈ X.dom, f x = ∑ i, a i * Q i x) → ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∀ x ∈ X.dom, X.fj la ξ ν f x = ∑ i, a i * X.fj la ξ ν (Q i) x := by
  first | exact @GlobalTheory.fj_eq_sum_of_eqOn_dom | exact GlobalTheory.fj_eq_sum_of_eqOn_dom | (intros; apply GlobalTheory.fj_eq_sum_of_eqOn_dom <;> assumption)
