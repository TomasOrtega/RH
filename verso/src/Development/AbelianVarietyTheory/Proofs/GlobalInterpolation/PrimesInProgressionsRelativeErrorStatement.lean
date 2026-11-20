import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeError
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FPrimesInProgressionsRelativeError.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.primesInProgressions_relativeError : GlobalTheory.Lin.PrimesRel := by
  first | exact @GlobalTheory.Lin.primesRel_holds | exact GlobalTheory.Lin.primesRel_holds | (intros; apply GlobalTheory.Lin.primesRel_holds <;> assumption)
