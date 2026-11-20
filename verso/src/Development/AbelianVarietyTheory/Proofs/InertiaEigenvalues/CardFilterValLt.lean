import Mathlib

namespace GlobalTheory.CardFilterLt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem card_filter_val_lt : ∀ {n h : ℕ}, h ≤ n → Finset.card {m : Fin n | (↑m : ℕ) < h} = h := by
  intro n h hh
  have key : (Finset.univ.filter (fun m : Fin n => (m : ℕ) < h)).map Fin.valEmbedding
      = Finset.range h := by
    ext k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm
    · intro hk
      exact ⟨⟨k, lt_of_lt_of_le hk hh⟩, hk, rfl⟩
  have hc := congrArg Finset.card key
  rwa [Finset.card_map, Finset.card_range] at hc

end GlobalTheory.CardFilterLt
