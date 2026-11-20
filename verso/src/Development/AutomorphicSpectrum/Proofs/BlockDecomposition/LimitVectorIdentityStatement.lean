import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitVectorIdentity
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.LimV.limVec | exact GlobalTheory.CompanionTheory.LimV.limVec | (intros; apply GlobalTheory.CompanionTheory.LimV.limVec <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.limit_vector_identity : PositivityTheory.Rg.BcB.SpectralAccumulation.LimVec := by
  first | exact @GlobalTheory.CompanionTheory.LimV.limVec | exact GlobalTheory.CompanionTheory.LimV.limVec | (intros; apply GlobalTheory.CompanionTheory.LimV.limVec <;> assumption)
