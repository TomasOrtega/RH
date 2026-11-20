import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLaw
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.wall_law_of_section_law : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw | exact GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw <;> assumption)
