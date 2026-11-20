import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitIndicatorGLBlockLiftBlockMatrixWithLastBasis.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_liftBlockMatrixWithLastBasis : ∀ (F : Type) [NormedField F] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ ≤ 1 → unitG (r + 1) F (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitG r F Z := by
  first | exact @GlobalTheory.JR.UnitGLift.unitG_lift | exact GlobalTheory.JR.UnitGLift.unitG_lift | (intros; apply GlobalTheory.JR.UnitGLift.unitG_lift <;> assumption)
