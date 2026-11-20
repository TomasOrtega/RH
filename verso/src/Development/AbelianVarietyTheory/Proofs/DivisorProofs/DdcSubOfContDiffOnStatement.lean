import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcSubOfContDiffOn
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ddc_sub_of_contDiffOn` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDdcSubOfContDiffOn.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.ddc_sub_of_contDiffOn' : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (Pt E g)} (u₁ u₂ : Pt E g → ℝ), IsOpen U → ContDiffOn ℝ 2 u₁ U → ContDiffOn ℝ 2 u₂ U → ∀ P ∈ U, ∀ v w : Pt E g, ddc (fun Q => u₁ Q - u₂ Q) P v w = ddc u₁ P v w - ddc u₂ P v w := by
  first | exact @GlobalTheory.ddc_sub_of_contDiffOn | exact GlobalTheory.ddc_sub_of_contDiffOn | (intros; apply GlobalTheory.ddc_sub_of_contDiffOn <;> assumption)
