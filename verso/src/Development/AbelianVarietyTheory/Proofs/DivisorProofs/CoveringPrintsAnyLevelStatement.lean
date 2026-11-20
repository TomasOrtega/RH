import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringHypAnyLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetHT.AnyLev.anyLev` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoveringHypAnyLevel.lean&line=211#L211)
-/
theorem _root_.GlobalTheory.T.anyLevSt_of_covering : GlobalTheory.CovTop.Hypotheses2 → AnyLevSt := by
  first | exact @GlobalTheory.DetHT.AnyLev.anyLev | exact GlobalTheory.DetHT.AnyLev.anyLev | (intros; apply GlobalTheory.DetHT.AnyLev.anyLev <;> assumption)
