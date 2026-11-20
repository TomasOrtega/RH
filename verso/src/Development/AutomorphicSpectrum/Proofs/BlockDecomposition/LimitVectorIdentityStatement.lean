import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitVectorIdentity
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLimitVectorIdentity.lean&line=274#L274)
-/
theorem _root_.GlobalTheory.T.limit_vector_identity : PositivityTheory.Rg.BcB.SpectralAccumulation.LimVec := by
  first | exact @GlobalTheory.CompanionTheory.LimV.limVec | exact GlobalTheory.CompanionTheory.LimV.limVec | (intros; apply GlobalTheory.CompanionTheory.LimV.limVec <;> assumption)
