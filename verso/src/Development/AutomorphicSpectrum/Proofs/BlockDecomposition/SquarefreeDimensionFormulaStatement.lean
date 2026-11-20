import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarefreeDimensionFormula
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSquarefreeDimensionFormula.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.squarefree_dimension_formula : ReciprocityTheory.Ty.Fin.St.SqfreeDimAll := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.sqfreeDimAll | exact GlobalTheory.CompanionTheory.TyFin.sqfreeDimAll | (intros; apply GlobalTheory.CompanionTheory.TyFin.sqfreeDimAll <;> assumption)
