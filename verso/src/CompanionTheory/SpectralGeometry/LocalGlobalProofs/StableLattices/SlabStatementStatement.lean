import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SlabStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FSlabStatement.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.SlabStatement : CompanionTheory.RgExh.Dec.N.S.Slab := by
  first | exact @GlobalTheory.CompanionTheory.SlabLemma.slab | exact GlobalTheory.CompanionTheory.SlabLemma.slab | (intros; apply GlobalTheory.CompanionTheory.SlabLemma.slab <;> assumption)
