import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRule
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RightRule.rightRule` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FNilpotentRightRule.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.NilpotentRightRule : CompanionTheory.RgExh.Dec.N.RightRule := by
  first | exact @GlobalTheory.CompanionTheory.RightRule.rightRule | exact GlobalTheory.CompanionTheory.RightRule.rightRule | (intros; apply GlobalTheory.CompanionTheory.RightRule.rightRule <;> assumption)
