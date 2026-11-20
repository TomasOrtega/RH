import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalStageNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.nonempty_locStage` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLocalStageNonempty.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.local_stage_nonempty : Nonempty GlobalTheory.Mem.LocStage := by
  first | exact @GlobalTheory.Mem.nonempty_locStage | exact GlobalTheory.Mem.nonempty_locStage | (intros; apply GlobalTheory.Mem.nonempty_locStage <;> assumption)
