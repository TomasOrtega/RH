import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergence
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgEisSide.sideConv | exact GlobalTheory.CompanionTheory.RgEisSide.sideConv | (intros; apply GlobalTheory.CompanionTheory.RgEisSide.sideConv <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.side_term_convergence : EpConv → TestSph → Lines → Term → SideConv := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSide.sideConv | exact GlobalTheory.CompanionTheory.RgEisSide.sideConv | (intros; apply GlobalTheory.CompanionTheory.RgEisSide.sideConv <;> assumption)
