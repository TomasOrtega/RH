import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExists
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.MassTest.testEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTestFunctionExists.lean&line=131#L131)
-/
theorem _root_.GlobalTheory.T.test_function_exists : TestEx := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassTest.testEx | exact GlobalTheory.CompanionTheory.SW.MassTest.testEx | (intros; apply GlobalTheory.CompanionTheory.SW.MassTest.testEx <;> assumption)
