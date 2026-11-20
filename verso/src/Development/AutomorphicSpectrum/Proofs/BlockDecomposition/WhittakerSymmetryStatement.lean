import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSymmetry
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.WhSymProof.whSym` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerSymmetry.lean&line=138#L138)
-/
theorem _root_.GlobalTheory.T.whittaker_symmetry : ReciprocityTheory.Ty.Fin.St.WhSym := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.WhSymProof.whSym | exact GlobalTheory.CompanionTheory.TyFin.WhSymProof.whSym | (intros; apply GlobalTheory.CompanionTheory.TyFin.WhSymProof.whSym <;> assumption)
