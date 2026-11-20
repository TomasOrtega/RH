import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationMatrixProperties
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPermutationMatrixProperties.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.permutation_matrix_properties : ReciprocityTheory.Ty.Fin.St.PmFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts | exact GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts <;> assumption)
