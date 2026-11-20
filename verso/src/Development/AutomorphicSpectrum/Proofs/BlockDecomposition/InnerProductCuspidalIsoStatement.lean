import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerProductCuspidalIso
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.IpIso.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FInnerProductCuspidalIso.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.inner_product_cuspidal_iso : ReciprocityTheory.Ty.Fin.St.IpCuspIso := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.IpIso.main | exact GlobalTheory.CompanionTheory.TyFin.IpIso.main | (intros; apply GlobalTheory.CompanionTheory.TyFin.IpIso.main <;> assumption)
