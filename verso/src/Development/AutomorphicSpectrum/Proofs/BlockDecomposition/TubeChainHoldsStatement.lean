import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeChainHolds
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.tube_chain_holds : PositivityTheory.RgEis.TubeChain := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.tubeChain | exact GlobalTheory.CompanionTheory.TubeFourier.tubeChain | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.tubeChain <;> assumption)
