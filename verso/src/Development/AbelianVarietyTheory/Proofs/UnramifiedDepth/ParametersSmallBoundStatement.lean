import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ParametersSmallBound
import Formalism.DropLevelBounds.Statement
open Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlowParameters.sizeDataSmall` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FParametersSmallBound.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.sizeData_small_bound : ParametersSmall := by
  first | exact @GlobalTheory.FlowParameters.sizeDataSmall | exact GlobalTheory.FlowParameters.sizeDataSmall | (intros; apply GlobalTheory.FlowParameters.sizeDataSmall <;> assumption)
