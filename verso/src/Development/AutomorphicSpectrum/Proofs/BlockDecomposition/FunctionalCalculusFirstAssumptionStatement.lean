import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 | exact GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 | (intros; apply GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.functional_calculus_first_assumption : PositivityTheory.RgBcC.Fc.Asm1 := by
  first | exact @GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 | exact GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 | (intros; apply GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 <;> assumption)
