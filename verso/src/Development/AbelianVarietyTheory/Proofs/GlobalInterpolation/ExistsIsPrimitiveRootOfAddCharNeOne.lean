import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `R K _ _ p hp hpR ψ hψ`. Take `⟨x, hx⟩` from `AddChar.ne_one_iff.mp hψ`. Establish `hpow : ψ x ^ p = 1`. Rewrite using `[← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hpR, zero_mul, AddChar.map_zero_eq_one]`. Use `haveI : Fact p.Prime := ⟨hp⟩`.

Establish `hord : orderOf (ψ x) = p` using `orderOf_eq_prime hpow hx`. Conclude with `⟨ψ x, hord ▸ IsPrimitiveRoot.orderOf (ψ x)⟩`.
-/
theorem exists_isPrimitiveRoot_of_addChar_ne_one :
    ∀ (R K : Type) [CommRing R] [Field K] (p : ℕ), p.Prime → (p : R) = 0 →
      ∀ ψ : AddChar R K, ψ ≠ 1 → ∃ ζ : K, IsPrimitiveRoot ζ p := by
  intro R K _ _ p hp hpR ψ hψ
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ
  have hpow : ψ x ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hpR, zero_mul, AddChar.map_zero_eq_one]
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (ψ x) = p := orderOf_eq_prime hpow hx
  exact ⟨ψ x, hord ▸ IsPrimitiveRoot.orderOf (ψ x)⟩

end GlobalTheory
