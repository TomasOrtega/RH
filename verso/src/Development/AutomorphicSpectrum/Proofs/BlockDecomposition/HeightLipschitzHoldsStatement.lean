import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightLipschitzHolds
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgEis.htLip | exact GlobalTheory.CompanionTheory.RgEis.htLip | (intros; apply GlobalTheory.CompanionTheory.RgEis.htLip <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.height_lipschitz_holds : PositivityTheory.RgEis.HtLip := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.htLip | exact GlobalTheory.CompanionTheory.RgEis.htLip | (intros; apply GlobalTheory.CompanionTheory.RgEis.htLip <;> assumption)
