import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormWedgePowerVanishes
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatTopPower.flatForm_wedgePow_succ_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatFormWedgePowerVanishes.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.flat_form_wedge_power_vanishes : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ P ∈ cov B g, ∀ v, wedgePow (om0 τ P) (g + 1) v = 0 := by
  first | exact @GlobalTheory.FlatTopPower.flatForm_wedgePow_succ_eq_zero | exact GlobalTheory.FlatTopPower.flatForm_wedgePow_succ_eq_zero | (intros; apply GlobalTheory.FlatTopPower.flatForm_wedgePow_succ_eq_zero <;> assumption)
