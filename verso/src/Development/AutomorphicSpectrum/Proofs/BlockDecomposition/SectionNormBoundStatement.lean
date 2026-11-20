import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.section_norm_bound : PositivityTheory.RgBcC.Fc.SecBound := by
  first | exact @GlobalTheory.CompanionTheory.SecBd.secBound_main | exact GlobalTheory.CompanionTheory.SecBd.secBound_main | (intros; apply GlobalTheory.CompanionTheory.SecBd.secBound_main <;> assumption)
