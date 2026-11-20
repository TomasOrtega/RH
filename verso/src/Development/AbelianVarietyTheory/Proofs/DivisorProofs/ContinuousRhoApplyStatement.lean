import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRhoApply
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContinuousRhoApply.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.continuous_rho_apply : ∀ (l : Type) [Fintype l] (v : L2 l), Continuous fun w : l ⊕ l → ℝ => rho w v := by
  first | exact @GlobalTheory.RealWeil.continuous_rho | exact GlobalTheory.RealWeil.continuous_rho | (intros; apply GlobalTheory.RealWeil.continuous_rho <;> assumption)
