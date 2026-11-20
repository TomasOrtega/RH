import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLaw
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgEisScale.scale` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEisensteinScalingLaw.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.eisenstein_scaling_law : PositivityTheory.RgEis.Scale := by
  first | exact @GlobalTheory.CompanionTheory.RgEisScale.scale | exact GlobalTheory.CompanionTheory.RgEisScale.scale | (intros; apply GlobalTheory.CompanionTheory.RgEisScale.scale <;> assumption)
