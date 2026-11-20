import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicFunctionFacts
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHolomorphicFunctionFacts.lean&line=312#L312)
-/
theorem _root_.GlobalTheory.T.holomorphic_function_facts : PositivityTheory.RgDs.K.HolFacts := by
  first | exact @GlobalTheory.CompanionTheory.HolOm.holFacts | exact GlobalTheory.CompanionTheory.HolOm.holFacts | (intros; apply GlobalTheory.CompanionTheory.HolOm.holFacts <;> assumption)
