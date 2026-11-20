import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealData
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwArch.archOnRecord_closed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FArchimedeanThetaCorrespondenceTowersRealData.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.archimedeanThetaCorrespondence_towers_real_data : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D := by
  first | exact @GlobalTheory.TwArch.archOnRecord_closed | exact GlobalTheory.TwArch.archOnRecord_closed | (intros; apply GlobalTheory.TwArch.archOnRecord_closed <;> assumption)
