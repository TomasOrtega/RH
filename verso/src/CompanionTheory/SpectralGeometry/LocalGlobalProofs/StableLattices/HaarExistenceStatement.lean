import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.ParabolicHaar.haarExists | exact GlobalTheory.CompanionTheory.ParabolicHaar.haarExists | (intros; apply GlobalTheory.CompanionTheory.ParabolicHaar.haarExists <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.HaarExistence : CompanionTheory.RgExh.Dec.L.HaarExists := by
  first | exact @GlobalTheory.CompanionTheory.ParabolicHaar.haarExists | exact GlobalTheory.CompanionTheory.ParabolicHaar.haarExists | (intros; apply GlobalTheory.CompanionTheory.ParabolicHaar.haarExists <;> assumption)
