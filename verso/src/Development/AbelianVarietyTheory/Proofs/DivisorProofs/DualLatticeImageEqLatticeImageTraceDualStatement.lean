import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.Statement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDualLatticeImageEqLatticeImageTraceDual.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  first | exact @GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | exact GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | (intros; apply GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual <;> assumption)
