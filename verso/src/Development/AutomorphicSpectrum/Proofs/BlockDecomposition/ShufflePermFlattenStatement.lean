import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlatten
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
open Zc.Comb
universe u
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FShufflePermFlatten.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.perm_flatten_of_shuffle : ∀ {T : Type u} (us : List (List T)) (w : List T), Shuffle us w → w.Perm us.flatten := by
  first | exact @GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten | exact GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten | (intros; apply GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten <;> assumption)
