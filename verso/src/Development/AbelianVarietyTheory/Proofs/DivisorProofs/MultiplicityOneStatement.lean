import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SteepMult.multOne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMultiplicityOneAlt.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.multOne' : GlobalTheory.RealLift.MultOne := by
  first | exact @GlobalTheory.SteepMult.multOne | exact GlobalTheory.SteepMult.multOne | (intros; apply GlobalTheory.SteepMult.multOne <;> assumption)
