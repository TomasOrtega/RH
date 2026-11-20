import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterLevelFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCharacterLevelFormula.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.character_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.PsiLev := by
  first | exact @GlobalTheory.CompanionTheory.GunrLev.psiLev_holds | exact GlobalTheory.CompanionTheory.GunrLev.psiLev_holds | (intros; apply GlobalTheory.CompanionTheory.GunrLev.psiLev_holds <;> assumption)
