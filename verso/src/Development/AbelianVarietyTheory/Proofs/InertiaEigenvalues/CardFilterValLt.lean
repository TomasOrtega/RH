import Mathlib

namespace GlobalTheory.CardFilterLt

/- English proof (translation)
Introduce `n h hh`. Establish `key : (Finset.univ.filter (fun m : Fin n => (m : ℕ) < h)).map Fin.valEmbedding = Finset.range h`. Use extensionality with `k`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, hm, rfl⟩`. Conclude with `hm`. Introduce `hk`. Conclude with `⟨⟨k, lt_of_lt_of_le hk hh⟩, hk, rfl⟩`. Establish `hc` using `congrArg Finset.card key`.

Rewrite `hc` using `[Finset.card_map, Finset.card_range]`. Then use the resulting hypothesis.
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
