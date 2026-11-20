import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
