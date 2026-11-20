import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FubiniOfParabolicHaarMultiple
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FFubiniOfParabolicHaarMultiple.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.fubini_of_parabolic_haar_multiple : CompanionTheory.RgExh.Dec.N.S.Fub2 → CompanionTheory.RgExh.Dec.N.S.Fub := by
  first | exact @GlobalTheory.CompanionTheory.RgFubOf.fubini_of_parabolic_multiple | exact GlobalTheory.CompanionTheory.RgFubOf.fubini_of_parabolic_multiple | (intros; apply GlobalTheory.CompanionTheory.RgFubOf.fubini_of_parabolic_multiple <;> assumption)
