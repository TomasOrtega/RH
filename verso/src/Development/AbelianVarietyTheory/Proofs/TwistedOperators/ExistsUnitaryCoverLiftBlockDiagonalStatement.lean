import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoverLiftBlockDiagonal
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolarU.exists_lift_blocks` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsUnitaryCoverLiftBlockDiagonal.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_unitaryCover_lift_blockDiagonal : ∀ (p q : ℕ) (T : GrpData p q), ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  first | exact @GlobalTheory.PolarU.exists_lift_blocks | exact GlobalTheory.PolarU.exists_lift_blocks | (intros; apply GlobalTheory.PolarU.exists_lift_blocks <;> assumption)
