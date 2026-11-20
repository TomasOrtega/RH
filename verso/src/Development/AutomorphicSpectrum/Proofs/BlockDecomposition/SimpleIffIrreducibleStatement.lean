import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSimpleIffIrreducible.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.simple_iff_irreducible : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | exact GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | (intros; apply GlobalTheory.CompanionTheory.TyFin.simpleIffIrr <;> assumption)
