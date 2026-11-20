import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweDualityUnitarySubstitutionSpanUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweOne.howeSpan_unit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHoweDualityUnitarySubstitutionSpanUnit.lean&line=173#L173)
-/
theorem _root_.GlobalTheory.T.howeDualityUnitarySubstitutionSpan_unit : HoweSpan Unit := by
  first | exact @GlobalTheory.HoweOne.howeSpan_unit | exact GlobalTheory.HoweOne.howeSpan_unit | (intros; apply GlobalTheory.HoweOne.howeSpan_unit <;> assumption)
