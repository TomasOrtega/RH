import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumTwoStageDescentUnipotent
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SatakeWeyl.descent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCellSumTwoStageDescentUnipotent.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.cell_sum_two_stage_descent_unipotent : GlobalTheory.SatakeWeyl.Descent := by
  first | exact @GlobalTheory.SatakeWeyl.descent | exact GlobalTheory.SatakeWeyl.descent | (intros; apply GlobalTheory.SatakeWeyl.descent <;> assumption)
