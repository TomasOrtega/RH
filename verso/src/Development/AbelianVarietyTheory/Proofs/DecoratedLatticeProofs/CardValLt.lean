import Mathlib

namespace GlobalTheory.CardValuationLt

/- English proof (translation)
Introduce `N n h`. Establish `hmap : ({i : Fin N | (↑i : ℕ) < n} : Finset (Fin N)).map Fin.valEmbedding = Finset.range n`. Use extensionality with `m`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, hi, rfl⟩`. Conclude with `hi`. Introduce `hm`. Conclude with `⟨⟨m, by omega⟩, hm, rfl⟩`. Rewrite using `[← Finset.card_map Fin.valEmbedding, hmap, Finset.card_range]`.
-/
theorem card_val_lt : ∀ (N n : ℕ), n ≤ N → Finset.card {i : Fin N | (↑i : ℕ) < n} = n := by
  intro N n h
  have hmap : ({i : Fin N | (↑i : ℕ) < n} : Finset (Fin N)).map Fin.valEmbedding = Finset.range n := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hm
      exact ⟨⟨m, by omega⟩, hm, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, Finset.card_range]

/- English proof (translation)
The claim follows from `card_val_lt`.
-/
example : ∀ (N n : ℕ), n ≤ N → Finset.card {i : Fin N | (↑i : ℕ) < n} = n := card_val_lt

end GlobalTheory.CardValuationLt
