import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FubiniParabolicMultiple
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.FubiniParabolicMultiple : CompanionTheory.RgExh.Dec.N.S.Fub2 := by
  first | exact @GlobalTheory.CompanionTheory.FubNM.fub2 | exact GlobalTheory.CompanionTheory.FubNM.fub2 | (intros; apply GlobalTheory.CompanionTheory.FubNM.fub2 <;> assumption)
