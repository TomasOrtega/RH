import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermStar
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDetStatement
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CtAdj.ctStar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FConstantTermStar.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.constant_term_star : PositivityTheory.Rg.BcB.F.MLM.CtStar := by
  first | exact @GlobalTheory.CompanionTheory.CtAdj.ctStar | exact GlobalTheory.CompanionTheory.CtAdj.ctStar | (intros; apply GlobalTheory.CompanionTheory.CtAdj.ctStar <;> assumption)
