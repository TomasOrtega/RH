import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMeasurePiChangeConstant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NabsDetEqOfActEq
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHaarMeasurePiChangeConstant.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.haar_measure_pi_change_constant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι] (ν νs : Measure k) (d : ι → kˣ), ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ F : (ι → k) → ℂ, ∫ e, F e ∂(Measure.pi fun _ => ν) = C * ∫ e, F (fun i => (d i : k) * e i) ∂(Measure.pi fun _ => νs) := by
  first | exact @GlobalTheory.IdealChain.integral_scale_change_haar | exact GlobalTheory.IdealChain.integral_scale_change_haar | (intros; apply GlobalTheory.IdealChain.integral_scale_change_haar <;> assumption)
