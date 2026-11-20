import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementP
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSinhcAdjointApplyMatrixUpperRightBlockElementP.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP : ∀ (p q : ℕ) (B C : Fin p → Fin q → ℂ), sAd (pY B) (pY C) = pY (sP (pY B) C) := by
  first | exact @GlobalTheory.PolarU.SinhcPres.sAd_pY | exact GlobalTheory.PolarU.SinhcPres.sAd_pY | (intros; apply GlobalTheory.PolarU.SinhcPres.sAd_pY <;> assumption)
