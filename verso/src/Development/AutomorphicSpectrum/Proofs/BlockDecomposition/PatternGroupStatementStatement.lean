import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPatternGroupStatement.lean&line=277#L277)
-/
theorem _root_.GlobalTheory.T.pattern_group_statement : ReciprocityTheory.Ty.Fin.St.PatGroup := by
  first | exact @GlobalTheory.CompanionTheory.PatGrp.patGroup | exact GlobalTheory.CompanionTheory.PatGrp.patGroup | (intros; apply GlobalTheory.CompanionTheory.PatGrp.patGroup <;> assumption)
