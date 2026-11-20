import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FConstantTermMultiplicative.lean&line=248#L248)
-/
theorem _root_.GlobalTheory.T.constant_term_multiplicative : CtMul := by
  first | exact @GlobalTheory.CompanionTheory.CtMulSplit.ctMul | exact GlobalTheory.CompanionTheory.CtMulSplit.ctMul | (intros; apply GlobalTheory.CompanionTheory.CtMulSplit.ctMul <;> assumption)
