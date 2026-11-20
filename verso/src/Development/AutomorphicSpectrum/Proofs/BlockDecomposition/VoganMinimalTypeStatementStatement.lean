import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VoganMinimalTypeStatement
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FVoganMinimalTypeStatement.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.vogan_minimal_type_statement : PositivityTheory.RgDs.Hilb.StepVogan := by
  first | exact @GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | exact GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | (intros; apply GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan <;> assumption)
