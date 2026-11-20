import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLaw
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgEisScale.scale | exact GlobalTheory.CompanionTheory.RgEisScale.scale | (intros; apply GlobalTheory.CompanionTheory.RgEisScale.scale <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.eisenstein_scaling_law : PositivityTheory.RgEis.Scale := by
  first | exact @GlobalTheory.CompanionTheory.RgEisScale.scale | exact GlobalTheory.CompanionTheory.RgEisScale.scale | (intros; apply GlobalTheory.CompanionTheory.RgEisScale.scale <;> assumption)
