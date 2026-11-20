import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FHaarExistence.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.HaarExistence : CompanionTheory.RgExh.Dec.L.HaarExists := by
  first | exact @GlobalTheory.CompanionTheory.ParabolicHaar.haarExists | exact GlobalTheory.CompanionTheory.ParabolicHaar.haarExists | (intros; apply GlobalTheory.CompanionTheory.ParabolicHaar.haarExists <;> assumption)
