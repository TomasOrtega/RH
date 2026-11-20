import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCharacterConductorCondition.lean&line=390#L390)
-/
theorem _root_.GlobalTheory.T.character_conductor_condition : PositivityTheory.SiegelWeilFormula.Gunr.PsiCond := by
  first | exact @GlobalTheory.CompanionTheory.PsiCondLoc.psiCond | exact GlobalTheory.CompanionTheory.PsiCondLoc.psiCond | (intros; apply GlobalTheory.CompanionTheory.PsiCondLoc.psiCond <;> assumption)
