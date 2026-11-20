import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBound
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigTop.Fun.existsIntegralMultiple` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FScalingFunctionBound.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.scaling_function_bound : GlobalTheory.BigTop.Fun.Scale := by
  first | exact @GlobalTheory.BigTop.Fun.existsIntegralMultiple | exact GlobalTheory.BigTop.Fun.existsIntegralMultiple | (intros; apply GlobalTheory.BigTop.Fun.existsIntegralMultiple <;> assumption)
