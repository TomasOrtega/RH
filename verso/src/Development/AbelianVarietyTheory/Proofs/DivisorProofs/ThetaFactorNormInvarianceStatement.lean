import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorNormInvariance
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReQuad
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.ThetaMet
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaMetInv.theta_metric_invariance` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaFactorNormInvariance.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.theta_factor_norm_invariance : ∀ {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ), GlobalTheory.IsSiegel τ → ∀ (l : Fl g) (z : Fin g → ℂ), Real.exp (-2 * π * ((fun i => ((z + per τ l) i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ fun i => ((z + per τ l) i).im))) * ‖Complex.exp (2 * π * Complex.I * thetaExp τ l z)‖ ^ 2 = Real.exp (-2 * π * ((fun i => (z i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ fun i => (z i).im))) := by
  first | exact @GlobalTheory.ThetaMetInv.theta_metric_invariance | exact GlobalTheory.ThetaMetInv.theta_metric_invariance | (intros; apply GlobalTheory.ThetaMetInv.theta_metric_invariance <;> assumption)
