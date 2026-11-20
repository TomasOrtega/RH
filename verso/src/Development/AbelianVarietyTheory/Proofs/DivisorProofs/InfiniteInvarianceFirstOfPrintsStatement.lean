import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteInvarianceFirstOfPublished
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInfiniteInvarianceFirstOfPublished.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.infinite_invariance_first_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.InfInvA := by
  first | exact @GlobalTheory.ThK.LemF.infInvA_holds | exact GlobalTheory.ThK.LemF.infInvA_holds | (intros; apply GlobalTheory.ThK.LemF.infInvA_holds <;> assumption)
