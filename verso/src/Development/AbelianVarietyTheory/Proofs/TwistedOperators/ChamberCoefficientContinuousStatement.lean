import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChamberCoefficientContinuous
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
open MeasureTheory GlobalTheory.Chamber
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FamCont.continuous_cM_expFam_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FChamberCoefficientContinuous.lean&line=132#L132)
-/
theorem _root_.GlobalTheory.T.chamber_coefficient_continuous : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅, ∀ (Z : Type) [TopologicalSpace Z] (X : Z → Finset (SV k) → A0 k), (∀ z, IsOrth 𝔞 (X z)) → (∀ P ∈ parP 𝔞 Q, Continuous fun z => X z P) → Continuous fun z => cM 𝔞 Q (expFam (X z)) 0 := by
  first | exact @GlobalTheory.FamCont.continuous_cM_expFam_zero | exact GlobalTheory.FamCont.continuous_cM_expFam_zero | (intros; apply GlobalTheory.FamCont.continuous_cM_expFam_zero <;> assumption)
