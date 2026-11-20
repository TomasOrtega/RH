import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntryHPAAtParameters
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FEntryHPAAtParameters.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.entry_hPA_at_parameters : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) R1.PeriodAdmissibilityAtBundlePoints := by
  first | exact @GlobalTheory.Fc.RL.PrimAt.at_linked | exact GlobalTheory.Fc.RL.PrimAt.at_linked | (intros; apply GlobalTheory.Fc.RL.PrimAt.at_linked <;> assumption)
