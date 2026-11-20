import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExchange
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RootExch.rootExchange | exact GlobalTheory.CompanionTheory.RootExch.rootExchange | (intros; apply GlobalTheory.CompanionTheory.RootExch.rootExchange <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.root_exchange' : ReciprocityTheory.Ty.Fin.St.RootExchange := by
  first | exact @GlobalTheory.CompanionTheory.RootExch.rootExchange | exact GlobalTheory.CompanionTheory.RootExch.rootExchange | (intros; apply GlobalTheory.CompanionTheory.RootExch.rootExchange <;> assumption)
