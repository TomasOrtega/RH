import Mathlib

namespace GlobalTheory.CompanionTheory.DivisorCount

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ]`. Use linear arithmetic over natural numbers and integers.
-/
private lemma two_mul_add_one_le_three_pow (k : ℕ) : 2 * k + 1 ≤ 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h : 1 ≤ 2 ^ k` using `Nat.one_le_two_pow`. Rewrite using `[pow_succ]`.

Use linear arithmetic over natural numbers and integers.
-/
private lemma two_mul_add_one_le_two_mul_two_pow (k : ℕ) : 2 * k + 1 ≤ 2 * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]; omega

/- English proof (translation)
Rewrite using `[← pow_mul, Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma card_divisors_sq_prime_pow {p k : ℕ} (hp : p.Prime) :
    (((p ^ k) ^ 2).divisors).card = 2 * k + 1 := by
  rw [← pow_mul, Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
  ring

/- English proof (translation)
Proceed by induction on `n using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p k hp hk`. Rewrite using `[card_divisors_sq_prime_pow hp]`. Break down `hp.eq_two_or_odd' with rfl | hodd` into its components or cases. Use `⟨?_, fun h => ?_⟩` and prove the remaining obligations.

Conclude with `two_mul_add_one_le_two_mul_two_pow k`. Conclude with `absurd h (by`. Rewrite using `[Nat.not_odd_iff_even]`. Conclude with `(Nat.even_pow.mpr ⟨even_two, hk.ne'⟩))`. Establish `h3 : 3 ≤ p`.

Use `hp.two_le` as an intermediate fact. Break down `hodd with ⟨m, rfl⟩` into its components or cases. Use linear arithmetic over natural numbers and integers. Establish `h : 2 * k + 1 ≤ p ^ k` using `(two_mul_add_one_le_three_pow k).trans (Nat.pow_le_pow_left h3 k)`. Conclude with `⟨by omega, fun _ => h⟩`.

Consider the case `zero => simp`. Consider the case `one => simp`. Consider the case `coprime a b ha hb hab iha ihb`. Establish `hcop : Nat.Coprime (a ^ 2) (b ^ 2)` using `Nat.Coprime.pow 2 2 hab`. Establish `hcard : ((a * b) ^ 2).divisors.card = (a ^ 2).divisors.card * (b ^ 2).divisors.card`.

Rewrite using `[mul_pow, hcop.card_divisors_mul]`. Rewrite using `[hcard]`. Establish `hodd : Odd a ∨ Odd b`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_or]`.

Establish `h1 : Even a` using `Nat.not_odd_iff_even.mp h.1`. Establish `h2 : Even b` using `Nat.not_odd_iff_even.mp h.2`. Establish `: 2 ∣ Nat.gcd a b` using `Nat.dvd_gcd h1.two_dvd h2.two_dvd`. Rewrite `this` using `[hab]`. Use linear arithmetic over natural numbers and integers.

Prove the components needed by the constructor for the conclusion. Break down `hodd with h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Introduce `h`.

Take `⟨h1, h2⟩` from `Nat.odd_mul.mp h`. Conclude with `Nat.mul_le_mul (iha.2 h1) (ihb.2 h2)`.
-/
theorem card_divisors_sq_le_strong (n : ℕ) :
    (n ^ 2).divisors.card ≤ 2 * n ∧ (Odd n → (n ^ 2).divisors.card ≤ n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [card_divisors_sq_prime_pow hp]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · refine ⟨?_, fun h => ?_⟩
      · exact two_mul_add_one_le_two_mul_two_pow k
      · exact absurd h (by
          rw [Nat.not_odd_iff_even]
          exact (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩))
    · have h3 : 3 ≤ p := by
        have := hp.two_le
        rcases hodd with ⟨m, rfl⟩
        omega
      have h : 2 * k + 1 ≤ p ^ k :=
        (two_mul_add_one_le_three_pow k).trans (Nat.pow_le_pow_left h3 k)
      exact ⟨by omega, fun _ => h⟩
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    have hcop : Nat.Coprime (a ^ 2) (b ^ 2) := Nat.Coprime.pow 2 2 hab
    have hcard : ((a * b) ^ 2).divisors.card
        = (a ^ 2).divisors.card * (b ^ 2).divisors.card := by
      rw [mul_pow, hcop.card_divisors_mul]
    rw [hcard]
    have hodd : Odd a ∨ Odd b := by
      by_contra h
      rw [not_or] at h
      have h1 : Even a := Nat.not_odd_iff_even.mp h.1
      have h2 : Even b := Nat.not_odd_iff_even.mp h.2
      have : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h1.two_dvd h2.two_dvd
      rw [hab] at this
      omega
    constructor
    · rcases hodd with h | h
      · calc _ ≤ a * (2 * b) := Nat.mul_le_mul (iha.2 h) ihb.1
          _ = 2 * (a * b) := by ring
      · calc _ ≤ (2 * a) * b := Nat.mul_le_mul iha.1 (ihb.2 h)
          _ = 2 * (a * b) := by ring
    · intro h
      obtain ⟨h1, h2⟩ := Nat.odd_mul.mp h
      exact Nat.mul_le_mul (iha.2 h1) (ihb.2 h2)

/- English proof (translation)
Conclude with `(card_divisors_sq_le_strong n).1` after adjusting the coercions.
-/
theorem card_divisors_sq_le_two_mul (n : ℕ) :
    (((n ^ 2).divisors.card : ℕ) : ℝ) ≤ 2 * n := by
  exact_mod_cast (card_divisors_sq_le_strong n).1

end GlobalTheory.CompanionTheory.DivisorCount
