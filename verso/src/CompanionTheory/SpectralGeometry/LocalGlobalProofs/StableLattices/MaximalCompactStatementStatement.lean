import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MaximalCompactStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgKMaj.kMaj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FMaximalCompactStatement.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.MaximalCompactStatement : CompanionTheory.RgExh.Dec.N.S.KMaj := by
  first | exact @GlobalTheory.CompanionTheory.RgKMaj.kMaj | exact GlobalTheory.CompanionTheory.RgKMaj.kMaj | (intros; apply GlobalTheory.CompanionTheory.RgKMaj.kMaj <;> assumption)
