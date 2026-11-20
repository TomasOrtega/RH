import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramified
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GunrLevChars.levChars` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLevelCharactersUnramified.lean&line=147#L147)
-/
theorem _root_.GlobalTheory.T.level_characters_unramified : PositivityTheory.SiegelWeilFormula.Gunr.LevChars := by
  first | exact @GlobalTheory.CompanionTheory.GunrLevChars.levChars | exact GlobalTheory.CompanionTheory.GunrLevChars.levChars | (intros; apply GlobalTheory.CompanionTheory.GunrLevChars.levChars <;> assumption)
