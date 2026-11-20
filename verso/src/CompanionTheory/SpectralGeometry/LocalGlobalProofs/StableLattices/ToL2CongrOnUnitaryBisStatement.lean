import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToL2CongrOnUnitaryBis
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FToL2CongrOnUnitaryBis.lean&line=461#L461)
-/
theorem _root_.GlobalTheory.T.rgExh_pack : CompanionTheory.RgExh.Dec.L.Pack := by
  first | exact @GlobalTheory.CompanionTheory.PackEmb.pack | exact GlobalTheory.CompanionTheory.PackEmb.pack | (intros; apply GlobalTheory.CompanionTheory.PackEmb.pack <;> assumption)
