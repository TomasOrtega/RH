import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceTestFunctions
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistenceTestFunctions.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.existence_test_functions : TestEx := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseTest.testEx | exact GlobalTheory.CompanionTheory.SW.BaseTest.testEx | (intros; apply GlobalTheory.CompanionTheory.SW.BaseTest.testEx <;> assumption)
