import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormSmoothOnCover
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatSmooth.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatFormSmoothOnCover.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.flat_form_smooth_on_cover : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ContDiffOn ℝ ∞ (om0 τ) (cov B g) := by
  first | exact @GlobalTheory.FlatSmooth.main | exact GlobalTheory.FlatSmooth.main | (intros; apply GlobalTheory.FlatSmooth.main <;> assumption)
