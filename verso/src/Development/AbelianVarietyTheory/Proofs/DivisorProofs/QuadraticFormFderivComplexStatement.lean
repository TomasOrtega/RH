import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFormFderivComplex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReQuad
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.ThetaMet
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaMetDc.dc_identity` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuadraticFormFderivComplex.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.quadratic_form_fderiv_complex : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ P ∈ cov B g, ∀ v : Pt E g, fderiv ℝ (quad τ) P (Complex.I • v) = fderiv ℝ (reQuad τ) P v + 2 * ∑ i, flat τ P (Sum.inl i) * dflat τ P v (Sum.inr i) := by
  first | exact @GlobalTheory.ThetaMetDc.dc_identity | exact GlobalTheory.ThetaMetDc.dc_identity | (intros; apply GlobalTheory.ThetaMetDc.dc_identity <;> assumption)
