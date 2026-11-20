import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportExists
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalSupportExists.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.cuspidal_support_exists : ReciprocityTheory.Ty.Fin.St.SupportExistsAll := by
  first | exact @GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll | exact GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll | (intros; apply GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll <;> assumption)
