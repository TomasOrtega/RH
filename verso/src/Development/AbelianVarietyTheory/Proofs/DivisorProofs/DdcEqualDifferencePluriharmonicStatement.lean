import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqualDifferencePluriharmonic
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDdcEqualDifferencePluriharmonic.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.ddc_equal_difference_pluriharmonic : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (B : Set E), IsOpen B → ∀ b ∈ B, ∀ F₁ F₂ : Pt E g → ℝ, ContDiffOn ℝ ∞ F₁ (cov B g) → ContDiffOn ℝ ∞ F₂ (cov B g) → (∀ P ∈ cov B g, ∀ v w : Pt E g, ddc F₁ P v w = ddc F₂ P v w) → ContDiff ℝ ∞ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) ∧ ∀ z a w : Fin g → ℂ, fderiv ℝ (fun y => fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) y (Complex.I • a)) z w = fderiv ℝ (fun y => fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) y (Complex.I • w)) z a := by
  first | exact @GlobalTheory.fibre_diff_ddc_eq_zero | exact GlobalTheory.fibre_diff_ddc_eq_zero | (intros; apply GlobalTheory.fibre_diff_ddc_eq_zero <;> assumption)
