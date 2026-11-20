import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleOfPerm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
open Zc.Comb
universe u
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FShuffleOfPerm.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.shuffle_of_perm : ∀ {T : Type u} (us us' : List (List T)) (w : List T), Shuffle us w → us.Perm us' → Shuffle us' w := by
  first | exact @GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm | exact GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm | (intros; apply GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm <;> assumption)
