import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasStrictFDerivAtExpTwoUpperRightBlockElementP
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHasStrictFDerivAtExpTwoUpperRightBlockElementP.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.hasStrictFDerivAt_exp_two_upperRightBlockElementP : ∀ (p q : ℕ) (B : Fin p → Fin q → ℂ), (∀ (V : Mat p q) (a b : Ix p q), HasDerivAt (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • V) a b) ((NormedSpace.exp (pY B) * sAd (pY B) V * NormedSpace.exp (pY B)) a b) 0) → ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B) := by
  first | exact @GlobalTheory.PolarU.hasStrictFDerivAt_exp_two_pY | exact GlobalTheory.PolarU.hasStrictFDerivAt_exp_two_pY | (intros; apply GlobalTheory.PolarU.hasStrictFDerivAt_exp_two_pY <;> assumption)
