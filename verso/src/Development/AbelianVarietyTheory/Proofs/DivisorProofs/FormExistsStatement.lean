import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CharPair.formEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormExists.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.FormExists : GlobalTheory.RealLift.FormEx := by
  first | exact @GlobalTheory.CharPair.formEx | exact GlobalTheory.CharPair.formEx | (intros; apply GlobalTheory.CharPair.formEx <;> assumption)
