import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

/- English proof (translation)
Unfold `pcnt`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Rewrite using `[Finset.ssubset_iff_of_subset]`. Use `⟨t, ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Introduce `s hs`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢`. Conclude with `⟨lt_trans hs.1 t.2, hs.2⟩`.
-/
theorem Comb.pcnt_lt_pcnt_of_eq {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w t (w t) < pcnt w n (w t) := by
  classical
  unfold pcnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨t, ?_, ?_⟩
    · simp
    · simp
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨lt_trans hs.1 t.2, hs.2⟩

/- English proof (translation)
Introduce `m lam w hw t`. Establish `hc : ∀ i, pcnt w (youngCells lam).card i = lam i`. Use `hw` as an intermediate fact. Simplify using `only [latticeWords, Finset.mem_filter, Finset.mem_univ, true_and] at this`. Conclude with `this.2`.

Establish `hlt : pcnt w t (w t) < lam (w t)`. Use `Comb.pcnt_lt_pcnt_of_eq w t` as an intermediate fact. Rewrite `this` using `[hc]`. Then use the resulting hypothesis. Establish `hle : lam (w t) ≤ ∑ i, lam i` using `Finset.single_le_sum (f := lam) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)`. Simplify using `only [youngCells, cellOfWord, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]`.

Conclude with `⟨lt_of_lt_of_le hlt hle, hlt⟩`.
-/
theorem CombCellOfWordMem.proof : CombCellOfWordMem.Statement := by
  intro m lam w hw t
  classical
  have hc : ∀ i, pcnt w (youngCells lam).card i = lam i := by
    have := hw
    simp only [latticeWords, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2
  have hlt : pcnt w t (w t) < lam (w t) := by
    have := Comb.pcnt_lt_pcnt_of_eq w t
    rwa [hc] at this
  have hle : lam (w t) ≤ ∑ i, lam i :=
    Finset.single_le_sum (f := lam) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  simp only [youngCells, cellOfWord, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    Finset.mem_range, true_and]
  exact ⟨lt_of_lt_of_le hlt hle, hlt⟩

end GroundTheory.Heights₂.Heights.RestTerms
