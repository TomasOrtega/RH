import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogPotentialFormula
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LeviLogChain.levi_poincare_chain` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeviFormLogPotentialFormula.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.levi_form_log_potential_formula : ∀ {e m : ℕ} (k : (Fin e → ℂ) → ℝ) (r : Fin m → (Fin e → ℂ) → ℝ) (c : ℝ) (z w : Fin e → ℂ), ContDiffAt ℝ 2 k z → (∀ i, ContDiffAt ℝ 2 (r i) z) → (∀ i, 0 < r i z) → 2 / Real.pi * levi (fun y => k y + -(c / 2) * ∑ i, Real.log (r i y)) z w = 2 / Real.pi * levi k z w + c * ∑ i, (1 / Real.pi * ((fderiv ℝ (r i) z w ^ 2 + fderiv ℝ (r i) z (Complex.I • w) ^ 2) / 4) / r i z ^ 2 - 1 / Real.pi * levi (r i) z w / r i z) := by
  first | exact @GlobalTheory.LeviLogChain.levi_poincare_chain | exact GlobalTheory.LeviLogChain.levi_poincare_chain | (intros; apply GlobalTheory.LeviLogChain.levi_poincare_chain <;> assumption)
