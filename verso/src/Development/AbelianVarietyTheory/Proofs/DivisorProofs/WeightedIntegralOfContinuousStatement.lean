import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralOfContinuous
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeightedIntegralOfContinuous.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.weighted_integral_of_continuous : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (g : M → ℝ),
    Continuous g → ∀ ψ : A.Fld, A.IsForm ψ → A.integral (A.fn g * ψ) = wInt A g ψ := by
  first | exact @GlobalTheory.LineForm.integral_fn_mul | exact GlobalTheory.LineForm.integral_fn_mul | (intros; apply GlobalTheory.LineForm.integral_fn_mul <;> assumption)
