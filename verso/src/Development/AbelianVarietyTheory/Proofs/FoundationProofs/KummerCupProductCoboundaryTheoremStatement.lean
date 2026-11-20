import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheorem
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FKummerCupProductCoboundaryTheorem.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.kummerCupProduct_coboundary_theorem : GlobalTheory.NeedB.ThmA := by
  first | exact @GlobalTheory.KummerCob.thmA | exact GlobalTheory.KummerCob.thmA | (intros; apply GlobalTheory.KummerCob.thmA <;> assumption)
