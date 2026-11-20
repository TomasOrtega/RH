import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCompositionForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmoothComp.smooth_comp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothCompositionForm.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.smooth_composition_form : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (f : M → ℝ) (s : Set ℝ) (G : ℝ → ℝ), Continuous f → A.SmoothOn Set.univ (fun y => (f y : ℂ)) →
    IsOpen s → (∀ y, f y ∈ s) → ContDiffOn ℝ (⊤ : ℕ∞) G s →
      Continuous (fun y => G (f y)) ∧ A.SmoothOn Set.univ (fun y => (G (f y) : ℂ)) ∧ A.IsForm (A.fn (fun y => G (f y))) := by
  first | exact @GlobalTheory.SmoothComp.smooth_comp | exact GlobalTheory.SmoothComp.smooth_comp | (intros; apply GlobalTheory.SmoothComp.smooth_comp <;> assumption)
