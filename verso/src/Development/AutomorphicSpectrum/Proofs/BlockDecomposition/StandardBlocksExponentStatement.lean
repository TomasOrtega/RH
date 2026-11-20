import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksExponent
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.StandardBlocks.stdBridge` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FStandardBlocksExponent.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.standard_blocks_exponent : PositivityTheory.Rg.BcB.F.Tail.PExp.StdBridge := by
  first | exact @GlobalTheory.CompanionTheory.StandardBlocks.stdBridge | exact GlobalTheory.CompanionTheory.StandardBlocks.stdBridge | (intros; apply GlobalTheory.CompanionTheory.StandardBlocks.stdBridge <;> assumption)
