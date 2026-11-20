import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ParametersSmallBound
import Formalism.DropLevelBounds.Statement
open Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FlowParameters.sizeDataSmall | exact GlobalTheory.FlowParameters.sizeDataSmall | (intros; apply GlobalTheory.FlowParameters.sizeDataSmall <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.sizeData_small_bound : ParametersSmall := by
  first | exact @GlobalTheory.FlowParameters.sizeDataSmall | exact GlobalTheory.FlowParameters.sizeDataSmall | (intros; apply GlobalTheory.FlowParameters.sizeDataSmall <;> assumption)
