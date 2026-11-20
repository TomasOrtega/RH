import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFacts
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.rgExh_flagFacts : CompanionTheory.RgExh.Dec.N.S.FlagFacts := by
  first | exact @GlobalTheory.CompanionTheory.GradFlag.flagFacts | exact GlobalTheory.CompanionTheory.GradFlag.flagFacts | (intros; apply GlobalTheory.CompanionTheory.GradFlag.flagFacts <;> assumption)
