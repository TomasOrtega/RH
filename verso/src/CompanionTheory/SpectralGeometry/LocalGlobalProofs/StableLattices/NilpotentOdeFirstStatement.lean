import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentOdeFirst
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FNilpotentOdeFirst.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.NilpotentOdeFirst : CompanionTheory.RgExh.Dec.N.OdeA := by
  first | exact @GlobalTheory.CompanionTheory.OdeRoots.odeA | exact GlobalTheory.CompanionTheory.OdeRoots.odeA | (intros; apply GlobalTheory.CompanionTheory.OdeRoots.odeA <;> assumption)
