import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHolds
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.section_law_holds : PositivityTheory.RgEis.SecLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSec.secLaw | exact GlobalTheory.CompanionTheory.RgEisSec.secLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisSec.secLaw <;> assumption)
