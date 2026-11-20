import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelInductionFromGallery
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgEis.sgStep | exact GlobalTheory.CompanionTheory.RgEis.sgStep | (intros; apply GlobalTheory.CompanionTheory.RgEis.sgStep <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.siegel_induction_from_gallery : PositivityTheory.RgEis.Gallery → PositivityTheory.RgEis.Transfer → PositivityTheory.RgEis.Twist → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.LeviS → PositivityTheory.RgEis.LeviQ → PositivityTheory.RgEis.ConvGrOf → PositivityTheory.RgEis.ConvU → PositivityTheory.RgEis.SgStep := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.sgStep | exact GlobalTheory.CompanionTheory.RgEis.sgStep | (intros; apply GlobalTheory.CompanionTheory.RgEis.sgStep <;> assumption)
