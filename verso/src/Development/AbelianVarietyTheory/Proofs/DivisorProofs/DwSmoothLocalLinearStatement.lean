import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DwSmoothLocalLinear
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HCA.dw_smooth_local_linear` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDwSmoothLocalLinear.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.dw_contDiffOn_local_linear : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)), (∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ (dw w u) U) ∧ (∀ u v : E d → ℂ, Set.EqOn u v U → Set.EqOn (dw w u) (dw w v) U) ∧ (∀ u v : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U → ∀ s t : ℂ, Set.EqOn (dw w (s • u + t • v)) (s • dw w u + t • dw w v) U) := by
  first | exact @GlobalTheory.HCA.dw_smooth_local_linear | exact GlobalTheory.HCA.dw_smooth_local_linear | (intros; apply GlobalTheory.HCA.dw_smooth_local_linear <;> assumption)
