import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormProductFormula
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FLogNormProductFormula.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.log_norm_product_formula : ∀ (N : ℕ) (P : Fin N → Prop) (t : ℂ) (v f : Fin N → ℂ) (e : Fin N → ℤ), t ≠ 0 → (∀ i, ¬ P i → v i ≠ 0 ∧ f i ≠ 0) → Real.log ‖t * ∏ i : Fin N, (if P i then 1 else v i * f i) ^ e i‖ = Real.log ‖t‖ + ∑ i : Fin N, (e i : ℝ) * (if P i then 0 else Real.log ‖v i‖ + Real.log ‖f i‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow <;> assumption)
