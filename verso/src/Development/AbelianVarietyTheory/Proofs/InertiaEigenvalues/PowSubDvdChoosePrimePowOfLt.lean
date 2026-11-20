import Mathlib
open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `l a c i hl hi hlt`. Take `⟨v, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hl.one_lt.ne'`. Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hi)`. Establish `hv : v ≤ c`. Establish `h1 : l ^ v ≤ l ^ v * m` using `Nat.le_mul_of_pos_right _ hm0`.

Establish `h2 : l ^ v < l ^ (c + 1)` using `lt_of_le_of_lt h1 hlt`. Use `(Nat.pow_lt_pow_iff_right hl.one_lt).1 h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hpos : 0 < l ^ a` using `pow_pos hl.pos a`. Establish `key : l ^ a ∣ l ^ v * m * (l ^ a).choose (l ^ v * m)`.

Take `⟨n, hn⟩ : ∃ n, l ^ a = n + 1` from `⟨l ^ a - 1, by omega⟩`. Take `⟨k, hk⟩ : ∃ k, l ^ v * m = k + 1` from `⟨l ^ v * m - 1, by omega⟩`. Rewrite using `[hn, hk]`. Use `⟨n.choose k, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Conclude with `(Nat.add_one_mul_choose_eq n k).symm`. Establish `h2 : l ^ (a - v) ∣ m * (l ^ a).choose (l ^ v * m)`. Break down `le_or_gt v a with h | h` into its components or cases. Establish `key' : l ^ v * l ^ (a - v) ∣ l ^ v * (m * (l ^ a).choose (l ^ v * m))`. Rewrite using `[← pow_add, Nat.add_sub_of_le h, ← mul_assoc]`.

Conclude with `key`. Conclude with `(Nat.mul_dvd_mul_iff_left (pow_pos hl.pos v)).1 key'`. Rewrite using `[show a - v = 0 by omega, pow_zero]`. Conclude with `one_dvd _`. Establish `hcop : (l ^ (a - v)).Coprime m` using `Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)`.

Establish `h3 : l ^ (a - v) ∣ (l ^ a).choose (l ^ v * m)` using `hcop.dvd_of_dvd_mul_left h2`. Conclude with `(pow_dvd_pow l (by omega : a - c ≤ a - v)).trans h3`.
-/
theorem pow_sub_dvd_choose_prime_pow_of_lt :
    ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by
  intro l a c i hl hi hlt
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hl.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hv : v ≤ c := by
    have h1 : l ^ v ≤ l ^ v * m := Nat.le_mul_of_pos_right _ hm0
    have h2 : l ^ v < l ^ (c + 1) := lt_of_le_of_lt h1 hlt
    have := (Nat.pow_lt_pow_iff_right hl.one_lt).1 h2
    omega
  have hpos : 0 < l ^ a := pow_pos hl.pos a
  have key : l ^ a ∣ l ^ v * m * (l ^ a).choose (l ^ v * m) := by
    obtain ⟨n, hn⟩ : ∃ n, l ^ a = n + 1 := ⟨l ^ a - 1, by omega⟩
    obtain ⟨k, hk⟩ : ∃ k, l ^ v * m = k + 1 := ⟨l ^ v * m - 1, by omega⟩
    rw [hn, hk]
    refine ⟨n.choose k, ?_⟩
    rw [mul_comm]
    exact (Nat.add_one_mul_choose_eq n k).symm
  have h2 : l ^ (a - v) ∣ m * (l ^ a).choose (l ^ v * m) := by
    rcases le_or_gt v a with h | h
    · have key' : l ^ v * l ^ (a - v) ∣ l ^ v * (m * (l ^ a).choose (l ^ v * m)) := by
        rw [← pow_add, Nat.add_sub_of_le h, ← mul_assoc]
        exact key
      exact (Nat.mul_dvd_mul_iff_left (pow_pos hl.pos v)).1 key'
    · rw [show a - v = 0 by omega, pow_zero]
      exact one_dvd _
  have hcop : (l ^ (a - v)).Coprime m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)
  have h3 : l ^ (a - v) ∣ (l ^ a).choose (l ^ v * m) := hcop.dvd_of_dvd_mul_left h2
  exact (pow_dvd_pow l (by omega : a - c ≤ a - v)).trans h3

end GlobalTheory
