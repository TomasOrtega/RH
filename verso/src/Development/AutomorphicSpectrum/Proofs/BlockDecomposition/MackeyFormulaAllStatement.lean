import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyFormulaAll
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMackeyFormulaAll.lean&line=222#L222)
-/
theorem _root_.GlobalTheory.T.mackey_formula_all : ReciprocityTheory.Ty.Fin.St.MackeyAll := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.mackeyAll | exact GlobalTheory.CompanionTheory.TyFin.mackeyAll | (intros; apply GlobalTheory.CompanionTheory.TyFin.mackeyAll <;> assumption)
