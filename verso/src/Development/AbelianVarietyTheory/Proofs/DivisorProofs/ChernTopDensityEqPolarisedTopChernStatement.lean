import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopDensityEqPolarisedTopChern
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodTop.chernTop_eq_mixTop` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChernTopDensityEqPolarisedTopChern.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.chernTopDensity_eq_polarisedTopChern : ∀ {n m : ℕ} (G : V n → Mat (fun _ : Unit => m) ℂ) (v : V n), chernTop (MvPolynomial.X ((), n)) G v = (Real.pi ^ n)⁻¹ * (mixTop fun _ => curvAt (fun u => G u ()) v).re := by
  first | exact @GlobalTheory.GoodTop.chernTop_eq_mixTop | exact GlobalTheory.GoodTop.chernTop_eq_mixTop | (intros; apply GlobalTheory.GoodTop.chernTop_eq_mixTop <;> assumption)
