import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelChartSupportedMulFormEqZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CxForm.LocStokes.integral_del_fn_mul_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralDelChartSupportedMulFormEqZero.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.del (A.fn χ * γ)) = 0 := by
  first | exact @GlobalTheory.CxForm.LocStokes.integral_del_fn_mul_eq_zero | exact GlobalTheory.CxForm.LocStokes.integral_del_fn_mul_eq_zero | (intros; apply GlobalTheory.CxForm.LocStokes.integral_del_fn_mul_eq_zero <;> assumption)
