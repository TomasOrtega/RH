import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FUMulPf.fuMul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteUnitaryMultiplication.lean&line=447#L447)
-/
theorem _root_.GlobalTheory.T.finite_unitary_multiplication : FUMul := by
  first | exact @GlobalTheory.CompanionTheory.FUMulPf.fuMul | exact GlobalTheory.CompanionTheory.FUMulPf.fuMul | (intros; apply GlobalTheory.CompanionTheory.FUMulPf.fuMul <;> assumption)
