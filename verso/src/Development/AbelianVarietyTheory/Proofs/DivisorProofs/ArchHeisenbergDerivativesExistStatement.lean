import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeisDer.derEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArchHeisenbergDerivativesExist.lean&line=232#L232)
-/
theorem _root_.GlobalTheory.T.archHeisenbergDerivatives_exist : GlobalTheory.RealLift.DerEx := by
  first | exact @GlobalTheory.HeisDer.derEx | exact GlobalTheory.HeisDer.derEx | (intros; apply GlobalTheory.HeisDer.derEx <;> assumption)
