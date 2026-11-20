import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusHalfLeviAbsDet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModulusHalfLeviAbsDet.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.modulus_half_levi_abs_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w), absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) : ℂ) := by
  first | exact @GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf | exact GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf | (intros; apply GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf <;> assumption)
