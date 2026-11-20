import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableExpNegHerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSummableExpNegHerm.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.summable_exp_neg_herm_add_norm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (C : ℝ), Summable (fun x : Λ => Real.exp (-(π / 2) * (H x x).re + C * ‖(x : V)‖)) := by
  first | exact @GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm | exact GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm | (intros; apply GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm <;> assumption)
