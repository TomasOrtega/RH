import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalTestFunctionExists
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.spherical_test_function_exists : PositivityTheory.RgEis.TestSph := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTestSph.testSph | exact GlobalTheory.CompanionTheory.RgEisTestSph.testSph | (intros; apply GlobalTheory.CompanionTheory.RgEisTestSph.testSph <;> assumption)
