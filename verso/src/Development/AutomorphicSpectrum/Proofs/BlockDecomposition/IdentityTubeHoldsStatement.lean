import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdentityTubeHolds
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Eis.idTube | exact GlobalTheory.CompanionTheory.Eis.idTube | (intros; apply GlobalTheory.CompanionTheory.Eis.idTube <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.identity_tube_holds : PositivityTheory.RgEis.IdTube := by
  first | exact @GlobalTheory.CompanionTheory.Eis.idTube | exact GlobalTheory.CompanionTheory.Eis.idTube | (intros; apply GlobalTheory.CompanionTheory.Eis.idTube <;> assumption)
