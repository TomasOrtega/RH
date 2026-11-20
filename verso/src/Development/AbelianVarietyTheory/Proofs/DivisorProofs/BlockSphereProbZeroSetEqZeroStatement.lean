import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereProbZeroSetEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.SJCoreA
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBlockSphereProbZeroSetEqZero.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.blockSphereProb_zeroSet_eq_zero_of_ne_zero : ∀ (B n : ℕ) (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g → blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  first | exact @GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero | exact GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero | (intros; apply GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero <;> assumption)
