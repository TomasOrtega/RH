import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEigenvalueStatement.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.EigenvalueStatement : EigSt := by
  first | exact @GlobalTheory.EigDiff.eigSt_holds | exact GlobalTheory.EigDiff.eigSt_holds | (intros; apply GlobalTheory.EigDiff.eigSt_holds <;> assumption)
