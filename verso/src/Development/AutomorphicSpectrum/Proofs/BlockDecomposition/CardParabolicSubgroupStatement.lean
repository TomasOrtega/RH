import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardParabolicSubgroup
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.FinGL.cardParab | exact GlobalTheory.CompanionTheory.FinGL.cardParab | (intros; apply GlobalTheory.CompanionTheory.FinGL.cardParab <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.card_parabolic_subgroup : ReciprocityTheory.Ty.Fin.St.CardParab := by
  first | exact @GlobalTheory.CompanionTheory.FinGL.cardParab | exact GlobalTheory.CompanionTheory.FinGL.cardParab | (intros; apply GlobalTheory.CompanionTheory.FinGL.cardParab <;> assumption)
