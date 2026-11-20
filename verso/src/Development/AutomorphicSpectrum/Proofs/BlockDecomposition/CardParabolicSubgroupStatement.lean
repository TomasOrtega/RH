import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardParabolicSubgroup
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FinGL.cardParab` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCardParabolicSubgroup.lean&line=180#L180)
-/
theorem _root_.GlobalTheory.T.card_parabolic_subgroup : ReciprocityTheory.Ty.Fin.St.CardParab := by
  first | exact @GlobalTheory.CompanionTheory.FinGL.cardParab | exact GlobalTheory.CompanionTheory.FinGL.cardParab | (intros; apply GlobalTheory.CompanionTheory.FinGL.cardParab <;> assumption)
