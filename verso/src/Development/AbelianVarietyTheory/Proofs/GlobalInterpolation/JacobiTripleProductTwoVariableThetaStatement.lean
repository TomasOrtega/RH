import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductTwoVariableTheta
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
open Complex
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.JacobiTriple.tripleProduct | exact GlobalTheory.JacobiTriple.tripleProduct | (intros; apply GlobalTheory.JacobiTriple.tripleProduct <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.jacobiTripleProduct_twoVariableTheta : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  first | exact @GlobalTheory.JacobiTriple.tripleProduct | exact GlobalTheory.JacobiTriple.tripleProduct | (intros; apply GlobalTheory.JacobiTriple.tripleProduct <;> assumption)
