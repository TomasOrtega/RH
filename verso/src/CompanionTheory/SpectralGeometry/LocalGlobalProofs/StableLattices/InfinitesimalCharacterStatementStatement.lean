import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FInfinitesimalCharacterStatement.lean&line=483#L483)
-/
theorem _root_.GlobalTheory.T.InfinitesimalCharacterStatement : CompanionTheory.RgExh.StepChar := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar | exact GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar <;> assumption)
