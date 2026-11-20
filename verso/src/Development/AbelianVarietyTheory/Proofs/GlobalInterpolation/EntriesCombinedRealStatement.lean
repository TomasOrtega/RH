import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EntriesCombinedReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fc.JoinLinked.at_selJ` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FEntriesCombinedReal.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.entries_combined_real : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) R1.PeriodAdmissibilityAtBundlePoints → RL.At (prmR N S Γ) R1.DecompositionConditionAtBundlePoints → RL.At (prmR N S Γ) RL.Row_tie → RL.At (prmR N S Γ) R1.JSelectionAtBundlePoints := by
  first | exact @GlobalTheory.Fc.JoinLinked.at_selJ | exact GlobalTheory.Fc.JoinLinked.at_selJ | (intros; apply GlobalTheory.Fc.JoinLinked.at_selJ <;> assumption)
