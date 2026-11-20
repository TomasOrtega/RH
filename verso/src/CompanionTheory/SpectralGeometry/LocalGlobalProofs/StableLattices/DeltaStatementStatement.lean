import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DeltaStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgFl.stDelta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FDeltaStatement.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.DeltaStatement : StDelta := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stDelta | exact GlobalTheory.CompanionTheory.RgFl.stDelta | (intros; apply GlobalTheory.CompanionTheory.RgFl.stDelta <;> assumption)
