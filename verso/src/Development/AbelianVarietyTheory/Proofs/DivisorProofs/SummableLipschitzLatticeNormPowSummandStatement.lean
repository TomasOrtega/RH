import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.Statement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LipschitzTR.summable_lhsTerm_ideal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSummableLipschitzLatticeNormPowSummand.lean&line=134#L134)
-/
theorem _root_.GlobalTheory.T.summable_lipschitzLatticeNormPowSummand : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 → ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Summable (fun a : (M : Set F) => lhsTerm k z a) := by
  first | exact @GlobalTheory.LipschitzTR.summable_lhsTerm_ideal | exact GlobalTheory.LipschitzTR.summable_lhsTerm_ideal | (intros; apply GlobalTheory.LipschitzTR.summable_lhsTerm_ideal <;> assumption)
