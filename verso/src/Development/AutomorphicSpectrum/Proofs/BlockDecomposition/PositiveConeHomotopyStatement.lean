import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeHomotopy
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SuperHomot.homot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPositiveConeHomotopy.lean&line=201#L201)
-/
theorem _root_.GlobalTheory.T.positive_cone_homotopy : PositivityTheory.RgBcC.Homot := by
  first | exact @GlobalTheory.CompanionTheory.SuperHomot.homot | exact GlobalTheory.CompanionTheory.SuperHomot.homot | (intros; apply GlobalTheory.CompanionTheory.SuperHomot.homot <;> assumption)
