import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConsequenceOfMackey
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FConsequenceOfMackey.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.consequence_of_mackey : ReciprocityTheory.Ty.Fin.St.FromMackey := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey | exact GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey | (intros; apply GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey <;> assumption)
