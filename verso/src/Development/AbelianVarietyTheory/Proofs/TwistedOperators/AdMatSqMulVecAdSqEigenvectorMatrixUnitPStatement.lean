import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitP
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FAdMatSqMulVecAdSqEigenvectorMatrixUnitP.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.adMat_sq_mulVec_adSqEigenvectorMatrixUnitP : ∀ (p q : ℕ) (h : ℕ → ℝ) (ab : PIx p q), (adMat (aOf p q h) ^ 2) *ᵥ eigP ab.1 = (((rootP h ab.1 : ℝ) : ℂ) ^ 2) • eigP ab.1 := by
  first | exact @GlobalTheory.PolarU.adMat_sq_mulVec_eigP | exact GlobalTheory.PolarU.adMat_sq_mulVec_eigP | (intros; apply GlobalTheory.PolarU.adMat_sq_mulVec_eigP <;> assumption)
