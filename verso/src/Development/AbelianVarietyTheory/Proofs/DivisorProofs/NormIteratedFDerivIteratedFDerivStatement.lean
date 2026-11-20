import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivIteratedFDeriv
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormIteratedFDerivIteratedFDeriv.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_iteratedFDeriv' : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n j : ℕ) (z : E), ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + j) f z‖ := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv | exact GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv | (intros; apply GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv <;> assumption)
