import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraDimension
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHarishChandraDimension.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.harish_chandra_dimension : ReciprocityTheory.Ty.Fin.St.HCDim := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.hcDim | exact GlobalTheory.CompanionTheory.TyFin.hcDim | (intros; apply GlobalTheory.CompanionTheory.TyFin.hcDim <;> assumption)
