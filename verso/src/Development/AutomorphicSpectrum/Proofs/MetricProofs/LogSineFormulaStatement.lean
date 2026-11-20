import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineFormula
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FLogSineFormula.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.log_sine_formula : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ), G.PosDef → a₀ ≠ a₁ → logSin G a₀ a₁ = Real.log ‖a₁ - a₀‖ + (1 / 2) * (xiPot G a₀ + xiPot G a₁) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin.logSin_eq_log_add_xiPot | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin.logSin_eq_log_add_xiPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin.logSin_eq_log_add_xiPot <;> assumption)
