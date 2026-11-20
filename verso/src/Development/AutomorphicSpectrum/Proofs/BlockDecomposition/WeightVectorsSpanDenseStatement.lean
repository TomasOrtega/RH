import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorsSpanDense
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeightVectorsSpanDense.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.weight_vectors_span_dense : PositivityTheory.RgDs.Hilb.StepWtSpan := by
  first | exact @GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan | exact GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan | (intros; apply GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan <;> assumption)
