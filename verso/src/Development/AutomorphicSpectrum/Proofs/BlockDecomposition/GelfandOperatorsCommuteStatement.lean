import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorsCommute
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.GelC.gelComm | exact GlobalTheory.CompanionTheory.GelC.gelComm | (intros; apply GlobalTheory.CompanionTheory.GelC.gelComm <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.gelfand_operators_commute : PositivityTheory.RgBcC.GelComm := by
  first | exact @GlobalTheory.CompanionTheory.GelC.gelComm | exact GlobalTheory.CompanionTheory.GelC.gelComm | (intros; apply GlobalTheory.CompanionTheory.GelC.gelComm <;> assumption)
