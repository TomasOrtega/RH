import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetHT.Covol.covol` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCovolumeStatement.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.CovolumeStatement : CovolSt := by
  first | exact @GlobalTheory.DetHT.Covol.covol | exact GlobalTheory.DetHT.Covol.covol | (intros; apply GlobalTheory.DetHT.Covol.covol <;> assumption)
