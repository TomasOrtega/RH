import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PolynomialNilpotentPath
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FPolynomialNilpotentPath.lean&line=399#L399)
-/
theorem _root_.GlobalTheory.T.PolynomialNilpotentPath : CompanionTheory.RgExh.Dec.L.PolyNilPath := by
  first | exact @GlobalTheory.CompanionTheory.PolyNilGrad.polyNilPath | exact GlobalTheory.CompanionTheory.PolyNilGrad.polyNilPath | (intros; apply GlobalTheory.CompanionTheory.PolyNilGrad.polyNilPath <;> assumption)
