import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceExists
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSplitPlaceExists.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.split_place_exists : SplitEx := by
  first | exact @GlobalTheory.CompanionTheory.SplitLevel.splitEx | exact GlobalTheory.CompanionTheory.SplitLevel.splitEx | (intros; apply GlobalTheory.CompanionTheory.SplitLevel.splitEx <;> assumption)
