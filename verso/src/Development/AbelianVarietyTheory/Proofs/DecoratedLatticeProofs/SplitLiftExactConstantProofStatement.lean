import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.liftExact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSplitLiftExactConstantProof.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.splitLiftExactConstant_proof : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  first | exact @GlobalTheory.FinPl.liftExact | exact GlobalTheory.FinPl.liftExact | (intros; apply GlobalTheory.FinPl.liftExact <;> assumption)
