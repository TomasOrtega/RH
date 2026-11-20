import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistence
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.wave_kernel_existence : PositivityTheory.RgBcC.AsmKerEx := by
  first | exact @GlobalTheory.CompanionTheory.WaveKer.asmKerEx | exact GlobalTheory.CompanionTheory.WaveKer.asmKerEx | (intros; apply GlobalTheory.CompanionTheory.WaveKer.asmKerEx <;> assumption)
