import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularity
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.KerFc.kerCore | exact GlobalTheory.CompanionTheory.KerFc.kerCore | (intros; apply GlobalTheory.CompanionTheory.KerFc.kerCore <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.kernel_regularity : PositivityTheory.RgBcC.Fc.KerCore := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.kerCore | exact GlobalTheory.CompanionTheory.KerFc.kerCore | (intros; apply GlobalTheory.CompanionTheory.KerFc.kerCore <;> assumption)
