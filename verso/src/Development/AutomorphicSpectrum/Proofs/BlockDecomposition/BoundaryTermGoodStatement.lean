import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgEisLeft.bGood | exact GlobalTheory.CompanionTheory.RgEisLeft.bGood | (intros; apply GlobalTheory.CompanionTheory.RgEisLeft.bGood <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.boundary_term_good : BGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLeft.bGood | exact GlobalTheory.CompanionTheory.RgEisLeft.bGood | (intros; apply GlobalTheory.CompanionTheory.RgEisLeft.bGood <;> assumption)
