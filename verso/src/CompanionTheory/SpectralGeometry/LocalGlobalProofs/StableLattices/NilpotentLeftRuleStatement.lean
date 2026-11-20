import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRule
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PathCoef.leftRule` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FNilpotentLeftRule.lean&line=230#L230)
-/
theorem _root_.GlobalTheory.T.NilpotentLeftRule : CompanionTheory.RgExh.Dec.N.LeftRule := by
  first | exact @GlobalTheory.CompanionTheory.PathCoef.leftRule | exact GlobalTheory.CompanionTheory.PathCoef.leftRule | (intros; apply GlobalTheory.CompanionTheory.PathCoef.leftRule <;> assumption)
