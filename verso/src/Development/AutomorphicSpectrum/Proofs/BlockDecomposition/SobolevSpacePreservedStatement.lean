import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpacePreserved
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.PresSobA.presSob | exact GlobalTheory.CompanionTheory.PresSobA.presSob | (intros; apply GlobalTheory.CompanionTheory.PresSobA.presSob <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.sobolev_space_preserved : PositivityTheory.RgBcC.Fc.PresSob := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.presSob | exact GlobalTheory.CompanionTheory.PresSobA.presSob | (intros; apply GlobalTheory.CompanionTheory.PresSobA.presSob <;> assumption)
