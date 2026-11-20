import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ s n ζ hn hζ z hz`. Use `haveI : NeZero n := ⟨hn.ne'⟩`. Establish `h1 : IsPrimitiveRoot (s ζ) n` using `hζ.map_of_injective s.injective`. Take `⟨i, -, hi⟩` from `h1.eq_pow_of_pow_eq_one hz`. Conclude with `⟨ζ ^ i, by rw [map_pow, hi]⟩`.
-/
theorem complex_rootOfUnity_mem_range_of_isPrimitiveRoot :
    ∀ (K : Type) [Field K] (s : K →+* ℂ) (n : ℕ) (ζ : K), 0 < n → IsPrimitiveRoot ζ n →
      ∀ z : ℂ, z ^ n = 1 → ∃ r : K, s r = z := by
  intro K _ s n ζ hn hζ z hz
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : IsPrimitiveRoot (s ζ) n := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

end GlobalTheory
