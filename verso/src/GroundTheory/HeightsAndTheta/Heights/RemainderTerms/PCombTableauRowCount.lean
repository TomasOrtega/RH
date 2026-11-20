import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

/- English proof (translation)
Introduce `m lam T t i`. Unfold `pcnt rowWord`. Apply `Finset.card_bij' (fun s _ => T.symm s) (fun p _ => T p)` to reduce the goal to its premises. Introduce `s hs`. Simplify using `only [mem_filter, mem_univ, true_and, Equiv.apply_symm_apply] at hs ⊢`.

Conclude with `⟨hs.2, hs.1⟩`. Introduce `p hp`. Simplify using `only [mem_filter, mem_univ, true_and, Equiv.symm_apply_apply] at hp ⊢`. Conclude with `⟨hp.2, hp.1⟩`. Introduce `s _`.

Simplify using the standard rewrite rules. Introduce `p _`. Simplify using the standard rewrite rules.
-/
theorem CombTableauRowCount.proof : CombTableauRowCount.Statement := by
  intro m lam T t i
  unfold pcnt rowWord
  apply Finset.card_bij' (fun s _ => T.symm s) (fun p _ => T p)
  · intro s hs
    simp only [mem_filter, mem_univ, true_and, Equiv.apply_symm_apply] at hs ⊢
    exact ⟨hs.2, hs.1⟩
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, Equiv.symm_apply_apply] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · intro s _
    simp
  · intro p _
    simp

end GroundTheory.Heights₂.Heights.RestTerms
