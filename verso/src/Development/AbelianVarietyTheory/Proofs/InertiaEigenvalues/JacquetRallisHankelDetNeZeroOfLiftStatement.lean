import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisHankelDetNeZeroOfLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJacquetRallisHankelDetNeZeroOfLift.lean&line=145#L145)
-/
theorem _root_.GlobalTheory.T.jacquetRallisHankelDet_ne_zero_of_lift : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k), Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by
  first | exact @GlobalTheory.JR.Step.delta_lift_ne | exact GlobalTheory.JR.Step.delta_lift_ne | (intros; apply GlobalTheory.JR.Step.delta_lift_ne <;> assumption)
