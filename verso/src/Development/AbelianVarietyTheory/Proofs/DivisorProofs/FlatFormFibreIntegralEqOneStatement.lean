import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormFibreIntegralEqOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatFormFibreIntegralEqOne.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.flat_form_fibre_integral_eq_one : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ b ∈ B, fibreInt τ (om0 τ) b = 1 := by
  first | exact @GlobalTheory.FibreInt.fibreIntegral_flatForm | exact GlobalTheory.FibreInt.fibreIntegral_flatForm | (intros; apply GlobalTheory.FibreInt.fibreIntegral_flatForm <;> assumption)
