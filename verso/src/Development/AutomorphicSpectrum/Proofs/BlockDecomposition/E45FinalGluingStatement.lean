import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.E45FinalGluing
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.EGlue.eFinalGlue` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FE45FinalGluing.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.e45_final_gluing : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.eFinalGlue | exact GlobalTheory.CompanionTheory.EGlue.eFinalGlue | (intros; apply GlobalTheory.CompanionTheory.EGlue.eFinalGlue <;> assumption)
