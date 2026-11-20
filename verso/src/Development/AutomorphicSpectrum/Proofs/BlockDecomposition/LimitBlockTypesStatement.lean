import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitBlockTypes
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLimitBlockTypes.lean&line=264#L264)
-/
theorem _root_.GlobalTheory.T.limit_block_types : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.BlockTypes := by
  first | exact @GlobalTheory.CompanionTheory.LimV.BlockTy.blockTypes | exact GlobalTheory.CompanionTheory.LimV.BlockTy.blockTypes | (intros; apply GlobalTheory.CompanionTheory.LimV.BlockTy.blockTypes <;> assumption)
