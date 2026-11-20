import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHolds
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgEis.stage | exact GlobalTheory.CompanionTheory.RgEis.stage | (intros; apply GlobalTheory.CompanionTheory.RgEis.stage <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.staged_estimate_holds : PositivityTheory.RgEis.PiLocalization₂ := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.stage | exact GlobalTheory.CompanionTheory.RgEis.stage | (intros; apply GlobalTheory.CompanionTheory.RgEis.stage <;> assumption)
