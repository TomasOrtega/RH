import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMetricIsMetricChernFlat
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.thetaMetric_isMetric_chernFlat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaMetricIsMetricChernFlat.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.chernIsFlat_exp_neg_im_quadratic : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → IsMetric B τ (stdLat g) (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2)) (fun P : Pt E g => Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)))) ∧ ChernIsFlat B τ (fun P : Pt E g => Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im)))) := by
  first | exact @GlobalTheory.thetaMetric_isMetric_chernFlat | exact GlobalTheory.thetaMetric_isMetric_chernFlat | (intros; apply GlobalTheory.thetaMetric_isMetric_chernFlat <;> assumption)
