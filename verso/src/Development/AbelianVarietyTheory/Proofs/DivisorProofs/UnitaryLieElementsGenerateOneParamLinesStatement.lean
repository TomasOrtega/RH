import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.unitaryLieElements_generate_oneParamLines : GlobalTheory.RealLift.LineEx := by
  first | exact @GlobalTheory.RealLift.exists_line_of_upq | exact GlobalTheory.RealLift.exists_line_of_upq | (intros; apply GlobalTheory.RealLift.exists_line_of_upq <;> assumption)
