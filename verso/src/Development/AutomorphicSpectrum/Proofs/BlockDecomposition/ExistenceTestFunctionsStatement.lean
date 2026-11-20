import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceTestFunctions
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.SW.BaseTest.testEx | exact GlobalTheory.CompanionTheory.SW.BaseTest.testEx | (intros; apply GlobalTheory.CompanionTheory.SW.BaseTest.testEx <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.existence_test_functions : TestEx := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseTest.testEx | exact GlobalTheory.CompanionTheory.SW.BaseTest.testEx | (intros; apply GlobalTheory.CompanionTheory.SW.BaseTest.testEx <;> assumption)
