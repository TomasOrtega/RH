import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweDualityUnitarySubstitutionSpanUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HoweOne.howeSpan_unit | exact GlobalTheory.HoweOne.howeSpan_unit | (intros; apply GlobalTheory.HoweOne.howeSpan_unit <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.howeDualityUnitarySubstitutionSpan_unit : HoweSpan Unit := by
  first | exact @GlobalTheory.HoweOne.howeSpan_unit | exact GlobalTheory.HoweOne.howeSpan_unit | (intros; apply GlobalTheory.HoweOne.howeSpan_unit <;> assumption)
