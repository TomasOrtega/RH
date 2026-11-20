import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeHomotopy
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SuperHomot.homot | exact GlobalTheory.CompanionTheory.SuperHomot.homot | (intros; apply GlobalTheory.CompanionTheory.SuperHomot.homot <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.positive_cone_homotopy : PositivityTheory.RgBcC.Homot := by
  first | exact @GlobalTheory.CompanionTheory.SuperHomot.homot | exact GlobalTheory.CompanionTheory.SuperHomot.homot | (intros; apply GlobalTheory.CompanionTheory.SuperHomot.homot <;> assumption)
