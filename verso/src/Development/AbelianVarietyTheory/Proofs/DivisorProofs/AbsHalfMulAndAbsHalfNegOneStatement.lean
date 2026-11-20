import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfMulAndAbsHalfNegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbsHalfMulAndAbsHalfNegOne.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.absHalf_mul_and_absHalf_neg_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), (∀ x y : w.adicCompletion E, x ≠ 0 → y ≠ 0 → absHalf w (x * y) = absHalf w x * absHalf w y) ∧ absHalf w (-1) = 1 := by
  first | exact @GlobalTheory.AbsHalf.absHalf_mul_neg_one | exact GlobalTheory.AbsHalf.absHalf_mul_neg_one | (intros; apply GlobalTheory.AbsHalf.absHalf_mul_neg_one <;> assumption)
