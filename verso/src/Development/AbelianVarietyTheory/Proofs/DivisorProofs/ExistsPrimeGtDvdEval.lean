import Mathlib

namespace GlobalTheory.PrimeDivisorOfPolynomialValue

open Polynomial

/- English proof (translation)
Establish `hdeg : 0 < (f.comp (C a * X)).natDegree`. Rewrite using `[natDegree_comp, natDegree_C_mul_X a ha, mul_one]`. Conclude with `hf`. Establish `hne : ∀ b : ℤ, f.comp (C a * X) - C b ≠ 0` using `fun b h => by`. Rewrite `h` using `[sub_eq_zero]`.

Rewrite `hdeg` using `[h, natDegree_C]`. Conclude with `lt_irrefl 0 hdeg`. Take `⟨k, hk⟩` from `Infinite.exists_notMem_finset ((f.comp (C a * X) - C c).roots.toFinset ∪ (f.comp (C a * X) - C (-c)).roots.toFinset)`. Use `⟨k, fun e => hk (Finset.mem_union_left _ ?_), fun e => hk (Finset.mem_union_right _ ?_)⟩` and prove the remaining obligations. Rewrite using `[Multiset.mem_toFinset, mem_roots (hne c)]`.

Simplify using `[e]`. Rewrite using `[Multiset.mem_toFinset, mem_roots (hne (-c))]`. Simplify using `[e]`.
-/
theorem exists_eval_mul_ne (f : ℤ[X]) (hf : 0 < f.natDegree) (c a : ℤ) (ha : a ≠ 0) :
    ∃ k : ℤ, f.eval (a * k) ≠ c ∧ f.eval (a * k) ≠ -c := by

  have hdeg : 0 < (f.comp (C a * X)).natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X a ha, mul_one]
    exact hf
  have hne : ∀ b : ℤ, f.comp (C a * X) - C b ≠ 0 := fun b h => by
    rw [sub_eq_zero] at h
    rw [h, natDegree_C] at hdeg
    exact lt_irrefl 0 hdeg
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset
    ((f.comp (C a * X) - C c).roots.toFinset ∪ (f.comp (C a * X) - C (-c)).roots.toFinset)
  refine ⟨k, fun e => hk (Finset.mem_union_left _ ?_), fun e => hk (Finset.mem_union_right _ ?_)⟩
  · rw [Multiset.mem_toFinset, mem_roots (hne c)]
    simp [e]
  · rw [Multiset.mem_toFinset, mem_roots (hne (-c))]
    simp [e]

/- English proof (translation)
Introduce `f hf n`. Establish `of_root : ∀ x, f.eval x = 0 → ∃ p, Nat.Prime p ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x`. Introduce `x hx`. Take `⟨p, hnp, hp⟩` from `Nat.exists_infinite_primes (n + 1)`. Conclude with `⟨p, hp, hnp, x, by rw [hx]; exact dvd_zero _⟩`.

Distinguish the cases in `h0 : f.eval 0 = 0`. Conclude with `of_root 0 h0`. Establish `hfac : ((n.factorial : ℕ) : ℤ) ≠ 0` using `by exact_mod_cast (Nat.factorial_pos n).ne'`. Take `⟨k, hk1, hk2⟩` from `exists_eval_mul_ne f hf (f.eval 0) _ (mul_ne_zero h0 hfac)`. Distinguish the cases in `hx : f.eval (f.eval 0 * n.factorial * k) = 0`.

Conclude with `of_root _ hx`. Take `⟨q, hq⟩` from `Polynomial.sub_dvd_eval_sub (f.eval 0 * n.factorial * k) 0 f`. Establish `hft : f.eval (f.eval 0 * n.factorial * k) = f.eval 0 * (1 + n.factorial * k * q)`. Take the linear combination `hq`. Establish `ht1 : (1 + (n.factorial : ℤ) * k * q) ≠ 1` using `fun h => hk1 (by rw [hft, h, mul_one])`.

Establish `ht2 : (1 + (n.factorial : ℤ) * k * q) ≠ -1` using `fun h => hk2 (by rw [hft, h, mul_neg_one])`. Establish `hnat : (1 + (n.factorial : ℤ) * k * q).natAbs ≠ 1`. Introduce `h`. Break down `Int.natAbs_eq_iff.1 h with h | h` into its components or cases. Conclude with `ht1 (by simpa using h)`.

Conclude with `ht2 (by simpa using h)`. Establish `hp` using `Nat.minFac_prime hnat`. Establish `hpt : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (1 + (n.factorial : ℤ) * k * q)` using `Int.ofNat_dvd_left.2 (Nat.minFac_dvd _)`. Use `⟨_, hp, ?_, _, by rw [hft]; exact dvd_mul_of_dvd_right hpt _⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hle`.

Rewrite `hle` using `[not_lt]`. Establish `h3 : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (n.factorial : ℤ) * k * q` using `dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial hp.pos hle)) _) _`. Establish `h4` using `dvd_sub hpt h3`. Rewrite `h4` using `[add_sub_cancel_right]`. Conclude with `hp.not_dvd_one (Int.natCast_dvd_natCast.1 (by simpa using h4))`.
-/
theorem exists_prime_gt_dvd_eval :
    ∀ (f : Polynomial ℤ), (0 : ℕ) < Polynomial.natDegree f → ∀ (n : ℕ),
      ∃ (p : ℕ), Nat.Prime p ∧ n < p ∧ ∃ (x : ℤ), (↑p : ℤ) ∣ Polynomial.eval x f := by
  intro f hf n

  have of_root : ∀ x, f.eval x = 0 → ∃ p, Nat.Prime p ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
    intro x hx
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hp, hnp, x, by rw [hx]; exact dvd_zero _⟩
  by_cases h0 : f.eval 0 = 0
  · exact of_root 0 h0
  have hfac : ((n.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  obtain ⟨k, hk1, hk2⟩ := exists_eval_mul_ne f hf (f.eval 0) _ (mul_ne_zero h0 hfac)
  by_cases hx : f.eval (f.eval 0 * n.factorial * k) = 0
  · exact of_root _ hx

  obtain ⟨q, hq⟩ := Polynomial.sub_dvd_eval_sub (f.eval 0 * n.factorial * k) 0 f
  have hft : f.eval (f.eval 0 * n.factorial * k) = f.eval 0 * (1 + n.factorial * k * q) := by
    linear_combination hq
  have ht1 : (1 + (n.factorial : ℤ) * k * q) ≠ 1 := fun h => hk1 (by rw [hft, h, mul_one])
  have ht2 : (1 + (n.factorial : ℤ) * k * q) ≠ -1 := fun h => hk2 (by rw [hft, h, mul_neg_one])
  have hnat : (1 + (n.factorial : ℤ) * k * q).natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq_iff.1 h with h | h
    · exact ht1 (by simpa using h)
    · exact ht2 (by simpa using h)
  have hp := Nat.minFac_prime hnat
  have hpt : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (1 + (n.factorial : ℤ) * k * q) :=
    Int.ofNat_dvd_left.2 (Nat.minFac_dvd _)
  refine ⟨_, hp, ?_, _, by rw [hft]; exact dvd_mul_of_dvd_right hpt _⟩

  by_contra hle
  rw [not_lt] at hle
  have h3 : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (n.factorial : ℤ) * k * q :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial hp.pos hle)) _) _
  have h4 := dvd_sub hpt h3
  rw [add_sub_cancel_right] at h4
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.1 (by simpa using h4))

end GlobalTheory.PrimeDivisorOfPolynomialValue
