import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolic
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.unipotent_convergence_of_parabolic : PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.ConvU := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw | exact GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw <;> assumption)
