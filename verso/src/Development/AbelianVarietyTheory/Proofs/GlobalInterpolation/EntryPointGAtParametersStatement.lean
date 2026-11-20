import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntryPointGAtParameters
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FEntryPointGAtParameters.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.entry_point_g_at_parameters : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) R1.DecompositionConditionAtBundlePoints := by
  first | exact @GlobalTheory.Fc.RL.at_hDcPtG | exact GlobalTheory.Fc.RL.at_hDcPtG | (intros; apply GlobalTheory.Fc.RL.at_hDcPtG <;> assumption)
