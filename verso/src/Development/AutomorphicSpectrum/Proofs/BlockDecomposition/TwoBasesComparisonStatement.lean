import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparison
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LinAlg.twoBases` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwoBasesComparison.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.two_bases_comparison : TwoBases := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.twoBases | exact GlobalTheory.CompanionTheory.LinAlg.twoBases | (intros; apply GlobalTheory.CompanionTheory.LinAlg.twoBases <;> assumption)
