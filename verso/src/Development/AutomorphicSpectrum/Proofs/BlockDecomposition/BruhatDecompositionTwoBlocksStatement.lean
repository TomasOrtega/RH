import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionTwoBlocks
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhatTwo` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBruhatDecompositionTwoBlocks.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.bruhat_decomposition_two_blocks : ReciprocityTheory.Ty.Fin.St.BruhatTwo := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhatTwo | exact GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhatTwo | (intros; apply GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhatTwo <;> assumption)
