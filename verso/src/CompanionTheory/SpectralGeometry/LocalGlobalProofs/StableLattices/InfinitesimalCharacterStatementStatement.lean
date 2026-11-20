import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar | exact GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.InfinitesimalCharacterStatement : CompanionTheory.RgExh.StepChar := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar | exact GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar <;> assumption)
