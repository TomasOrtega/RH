import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `m hm`. Establish `hsupp : (Function.support fun p : ℕ => if p.Prime then (padicValNat p m : ℝ) * Real.log p else 0) ⊆ (m.primeFactors : Set ℕ)`. Introduce `p hp`. Simplify using `only [Function.mem_support, ne_eq] at hp`. Distinguish the cases in `hpp : p.Prime`.

Rewrite `hp` using `[if_pos hpp]`. Establish `h0 : padicValNat p m ≠ 0`. Introduce `h`. Apply `hp` to reduce the goal to its premises. Simplify using `[h]`.

Establish `hdvd : p ∣ m`. Assume the negation of the conclusion as `hnd`. Conclude with `h0 (padicValNat.eq_zero_of_not_dvd hnd)`. Simplify using `only [Finset.mem_coe, Nat.mem_primeFactors]`. Conclude with `⟨hpp, hdvd, hm⟩`.

Conclude with `absurd (if_neg hpp) hp`. Use `⟨(Finset.finite_toSet _).subset hsupp, ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hpp : p.Prime` using `Nat.prime_of_mem_primeFactors hp`.

Rewrite using `[if_pos hpp, Nat.factorization_def m hpp]`.
-/
theorem finsum_padicValNat_mul_log_eq_log :
    ∀ m : ℕ, m ≠ 0 → (Function.support fun p : ℕ => if p.Prime then (padicValNat p m : ℝ) * Real.log p else 0).Finite ∧ ∑ᶠ p : ℕ, (if p.Prime then (padicValNat p m : ℝ) * Real.log p else 0) = Real.log m := by
  intro m hm
  have hsupp : (Function.support fun p : ℕ => if p.Prime then (padicValNat p m : ℝ) * Real.log p else 0) ⊆ (m.primeFactors : Set ℕ) := by
    intro p hp
    simp only [Function.mem_support, ne_eq] at hp
    by_cases hpp : p.Prime
    · rw [if_pos hpp] at hp
      have h0 : padicValNat p m ≠ 0 := by
        intro h; apply hp; simp [h]
      have hdvd : p ∣ m := by
        by_contra hnd
        exact h0 (padicValNat.eq_zero_of_not_dvd hnd)
      simp only [Finset.mem_coe, Nat.mem_primeFactors]
      exact ⟨hpp, hdvd, hm⟩
    · exact absurd (if_neg hpp) hp
  refine ⟨(Finset.finite_toSet _).subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Real.log_nat_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [if_pos hpp, Nat.factorization_def m hpp]

end GlobalTheory
