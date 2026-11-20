import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelWeightFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.KerWord.kerW | exact GlobalTheory.CompanionTheory.KerWord.kerW | (intros; apply GlobalTheory.CompanionTheory.KerWord.kerW <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.kernel_weight_facts : PositivityTheory.RgBcC.Fc.KerW := by
  first | exact @GlobalTheory.CompanionTheory.KerWord.kerW | exact GlobalTheory.CompanionTheory.KerWord.kerW | (intros; apply GlobalTheory.CompanionTheory.KerWord.kerW <;> assumption)
