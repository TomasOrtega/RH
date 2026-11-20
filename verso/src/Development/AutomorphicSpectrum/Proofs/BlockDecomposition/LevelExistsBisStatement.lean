import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExistsBis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LevelU.levelEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelExistsBis.lean&line=379#L379)
-/
theorem _root_.GlobalTheory.T.level_exists_bis : LevelEx := by
  first | exact @GlobalTheory.CompanionTheory.LevelU.levelEx | exact GlobalTheory.CompanionTheory.LevelU.levelEx | (intros; apply GlobalTheory.CompanionTheory.LevelU.levelEx <;> assumption)
