import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRegularLocalStatement.lean&line=144#L144)
-/
theorem _root_.GlobalTheory.T.RegularLocalStatement : RegLocSt := by
  first | exact @GlobalTheory.DetHT.RegLoc.main | exact GlobalTheory.DetHT.RegLoc.main | (intros; apply GlobalTheory.DetHT.RegLoc.main <;> assumption)
