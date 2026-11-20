import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.finite_propagation_speed_holds : PositivityTheory.RgBcC.AsmSpeed := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.asmSpeed | exact GlobalTheory.CompanionTheory.WaveSpd.asmSpeed | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.asmSpeed <;> assumption)
