import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianIteratedFDerivWeightedExpBounded
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaussDerivBound.weighted_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaussianIteratedFDerivWeightedExpBounded.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c α : ℝ), 0 < c → α < 1 → ∀ (k m : ℕ),
    ∃ K : ℝ, ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
      Real.exp (c * α * ‖y‖ ^ 2) ≤ K := by
  first | exact @GlobalTheory.GaussDerivBound.weighted_bound | exact GlobalTheory.GaussDerivBound.weighted_bound | (intros; apply GlobalTheory.GaussDerivBound.weighted_bound <;> assumption)
