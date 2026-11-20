import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExchange
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RootExch.rootExchange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRootExchange.lean&line=398#L398)
-/
theorem _root_.GlobalTheory.T.root_exchange' : ReciprocityTheory.Ty.Fin.St.RootExchange := by
  first | exact @GlobalTheory.CompanionTheory.RootExch.rootExchange | exact GlobalTheory.CompanionTheory.RootExch.rootExchange | (intros; apply GlobalTheory.CompanionTheory.RootExch.rootExchange <;> assumption)
