import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitNodeEmbedding
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TreeNode.nodeEmb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLimitNodeEmbedding.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.limit_node_embedding : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.NodeEmb := by
  first | exact @GlobalTheory.CompanionTheory.TreeNode.nodeEmb | exact GlobalTheory.CompanionTheory.TreeNode.nodeEmb | (intros; apply GlobalTheory.CompanionTheory.TreeNode.nodeEmb <;> assumption)
