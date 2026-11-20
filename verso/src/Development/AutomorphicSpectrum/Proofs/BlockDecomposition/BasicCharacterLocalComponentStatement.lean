import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicCharacterLocalComponent
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBasicCharacterLocalComponent.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.basic_character_unramified : PositivityTheory.SiegelWeilFormula.Gunr.PsiBasic := by
  first | exact @GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic | exact GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic | (intros; apply GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic <;> assumption)
