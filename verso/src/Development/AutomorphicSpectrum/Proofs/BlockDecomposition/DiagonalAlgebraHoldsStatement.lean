import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalAlgebraHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDiagonalAlgebraHolds.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.diagonal_algebra_holds : DiagAlg := by
  first | exact @GlobalTheory.CompanionTheory.BlockScalars.diagAlg | exact GlobalTheory.CompanionTheory.BlockScalars.diagAlg | (intros; apply GlobalTheory.CompanionTheory.BlockScalars.diagAlg <;> assumption)
