import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTau
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeDuality.GlRelTau

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.CapelliTwist.qdetTau | exact GlobalTheory.CompanionTheory.CapelliTwist.qdetTau | (intros; apply GlobalTheory.CompanionTheory.CapelliTwist.qdetTau <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.QuantumDeterminantTau : CompanionTheory.RgExh.Hk.QdetTau := by
  first | exact @GlobalTheory.CompanionTheory.CapelliTwist.qdetTau | exact GlobalTheory.CompanionTheory.CapelliTwist.qdetTau | (intros; apply GlobalTheory.CompanionTheory.CapelliTwist.qdetTau <;> assumption)
