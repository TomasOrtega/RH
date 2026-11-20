import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaMinor
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.OmegaMinor : CompanionTheory.RgExh.Hk.OmMinor := by
  first | exact @GlobalTheory.CompanionTheory.HeckeCapelli.omMinor | exact GlobalTheory.CompanionTheory.HeckeCapelli.omMinor | (intros; apply GlobalTheory.CompanionTheory.HeckeCapelli.omMinor <;> assumption)
