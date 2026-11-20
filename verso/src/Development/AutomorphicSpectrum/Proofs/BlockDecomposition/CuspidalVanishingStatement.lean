import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalVanishing
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalVanishing.lean&line=226#L226)
-/
theorem _root_.GlobalTheory.T.cuspidal_vanishing : ReciprocityTheory.Ty.Fin.St.CuspVanish := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspVan.cuspVanish | exact GlobalTheory.CompanionTheory.TyFin.CuspVan.cuspVanish | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspVan.cuspVanish <;> assumption)
