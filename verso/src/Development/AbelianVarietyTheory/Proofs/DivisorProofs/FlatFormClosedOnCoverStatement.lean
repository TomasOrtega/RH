import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormClosedOnCover
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatClosed.extDeriv_om0` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatFormClosedOnCover.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.flat_form_closed_on_cover : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ P ∈ cov B g, extDeriv (om0 τ) P = 0 := by
  first | exact @GlobalTheory.FlatClosed.extDeriv_om0 | exact GlobalTheory.FlatClosed.extDeriv_om0 | (intros; apply GlobalTheory.FlatClosed.extDeriv_om0 <;> assumption)
