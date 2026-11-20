import Mathlib

open scoped NNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ R O _ _ _ _ _ x e he hH ψ ψ' h`. Use extensionality with `y`. Rewrite using `[← sub_eq_zero]`. Apply `hH.haus` to reduce the goal to its premises. Introduce `n`.

Rewrite using `[SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨z, rfl⟩ : ∃ z : R, z ^ l ^ n = y` from `⟨(iterateFrobeniusEquiv R l n).symm y, by`. Establish `hs` using `(iterateFrobeniusEquiv R l n).apply_symm_apply y`. Rewrite using `[iterateFrobeniusEquiv_apply, iterateFrobenius_def] at hs⟩` and apply the resulting hypothesis. Rewrite using `[map_pow, map_pow, ← sub_pow_char_pow]`.

Establish `hl : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hn : n ≤ e * l ^ n` using `(Nat.lt_pow_self (by omega)).le.trans (Nat.le_mul_of_pos_left _ he)`. Conclude with `(pow_dvd_pow x hn).trans (by rw [pow_mul]; exact pow_dvd_pow_of_dvd (h z) _)`.
-/
theorem ringHom_eq_of_perfect_of_dvd_sub :
    ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  intro l _ R O _ _ _ _ _ x e he hH ψ ψ' h
  ext y
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  obtain ⟨z, rfl⟩ : ∃ z : R, z ^ l ^ n = y :=
    ⟨(iterateFrobeniusEquiv R l n).symm y, by
      have hs := (iterateFrobeniusEquiv R l n).apply_symm_apply y
      rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at hs⟩
  rw [map_pow, map_pow, ← sub_pow_char_pow]
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hn : n ≤ e * l ^ n :=
    (Nat.lt_pow_self (by omega)).le.trans (Nat.le_mul_of_pos_left _ he)
  exact (pow_dvd_pow x hn).trans (by rw [pow_mul]; exact pow_dvd_pow_of_dvd (h z) _)

end GlobalTheory
