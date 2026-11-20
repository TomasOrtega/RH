import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSliceSmoothAndMatrixUnitAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeviSliceSmoothAndMatrixUnitAction.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.leviSlice_smooth_and_matrixUnit_action : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a), (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) ∧ ∀ (τ : E →+* ℂ) (p p' : Fin (a - r)) (ψ : Sm E (a - r)), ψ.1 = (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) → (Eop τ p p' ψ).1 = fun m₂ : GA E (a - r) => (Eop τ (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  first | exact @GlobalTheory.LeviSliceGA.slice_smooth_Eop | exact GlobalTheory.LeviSliceGA.slice_smooth_Eop | (intros; apply GlobalTheory.LeviSliceGA.slice_smooth_Eop <;> assumption)
