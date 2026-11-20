import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealLiftGen.genEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOneParamSubgroupGeneratorsExist.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.oneParamSubgroup_generators_exist : GlobalTheory.RealLift.GenEx := by
  first | exact @GlobalTheory.RealLiftGen.genEx | exact GlobalTheory.RealLiftGen.genEx | (intros; apply GlobalTheory.RealLiftGen.genEx <;> assumption)
