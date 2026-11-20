import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerInnerProduct
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.intwIp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntertwinerInnerProduct.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.intertwiner_inner_product : ReciprocityTheory.Ty.Fin.St.IntwIp := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.intwIp | exact GlobalTheory.CompanionTheory.TyFin.intwIp | (intros; apply GlobalTheory.CompanionTheory.TyFin.intwIp <;> assumption)
