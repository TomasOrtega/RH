import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlocksExponent
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDeltaBlocksExponent.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.delta_blocks_exponent : PositivityTheory.Rg.BcB.F.Tail.PExp.DlBridge := by
  first | exact @GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge | exact GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge | (intros; apply GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge <;> assumption)
