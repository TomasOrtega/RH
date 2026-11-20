import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityInnerProduct
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.frobIp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFrobeniusReciprocityInnerProduct.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.frobenius_reciprocity_inner_product : ReciprocityTheory.Ty.Fin.St.FrobIp := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.frobIp | exact GlobalTheory.CompanionTheory.TyFin.frobIp | (intros; apply GlobalTheory.CompanionTheory.TyFin.frobIp <;> assumption)
