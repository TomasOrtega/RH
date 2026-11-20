import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionDistribHaarCharEqAbsHalfSq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ModAbs.haar_eq_absHalf_sq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdicCompletionDistribHaarCharEqAbsHalfSq.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.adicCompletion_distribHaarChar_eq_absHalf_sq : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) (hx : x ≠ 0), (((MeasureTheory.distribHaarChar (w.adicCompletion E) (Units.mk0 x hx) : NNReal) : ℝ) : ℂ) = absHalf w x ^ 2 := by
  first | exact @GlobalTheory.ModAbs.haar_eq_absHalf_sq | exact GlobalTheory.ModAbs.haar_eq_absHalf_sq | (intros; apply GlobalTheory.ModAbs.haar_eq_absHalf_sq <;> assumption)
