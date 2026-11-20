import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentOdeSecond
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.OdeRoots.Above.odeB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FNilpotentOdeSecond.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.NilpotentOdeSecond : CompanionTheory.RgExh.Dec.N.OdeB := by
  first | exact @GlobalTheory.CompanionTheory.OdeRoots.Above.odeB | exact GlobalTheory.CompanionTheory.OdeRoots.Above.odeB | (intros; apply GlobalTheory.CompanionTheory.OdeRoots.Above.odeB <;> assumption)
