import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionUnique
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBruhatDecompositionUnique.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.bruhat_decomposition_unique : ReciprocityTheory.Ty.Fin.St.BruhatUniq := by
  first | exact @GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq | exact GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq | (intros; apply GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq <;> assumption)
