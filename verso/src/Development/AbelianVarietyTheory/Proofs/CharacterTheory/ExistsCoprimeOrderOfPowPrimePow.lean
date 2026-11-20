import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨k, u, hu, h⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `h1 : orderOf (x ^ p ^ k) ∣ u`. Apply `orderOf_dvd_of_pow_eq_one` to reduce the goal to its premises. Rewrite using `[← pow_mul, ← h, pow_orderOf_eq_one]`.

Conclude with `Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu).symm`.
-/
theorem exists_coprime_orderOf_pow_prime_pow (G : Type) [Group G] [Finite G] (x : G) (p : ℕ)
    (hp : p.Prime) : ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  obtain ⟨k, u, hu, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  refine ⟨k, ?_⟩
  have h1 : orderOf (x ^ p ^ k) ∣ u := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← h, pow_orderOf_eq_one]
  exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu).symm

end GlobalTheory
