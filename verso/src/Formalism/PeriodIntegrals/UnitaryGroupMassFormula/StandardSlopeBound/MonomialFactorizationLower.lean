import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaBasis

namespace PI.SlopeSteps

open Finset

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem multinomial_le_pow {N : ℕ} (f : Fin N → ℕ) : Nat.multinomial univ f ≤ N ^ (∑ a, f a) := by
  have h := Finset.sum_pow_eq_sum_piAntidiag (R := ℕ) (univ : Finset (Fin N)) (fun _ => (1 : ℕ)) (∑ a, f a)
  simp only [one_pow, prod_const_one, mul_one, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  rw [h]
  exact Finset.single_le_sum (f := fun k => Nat.multinomial univ k) (fun _ _ => Nat.zero_le _)
    (mem_piAntidiag.mpr ⟨rfl, fun i _ => mem_univ i⟩)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem col_fact_le {N : ℕ} (f : Fin N → ℕ) :
    (∑ a, f a).factorial ≤ N ^ (∑ a, f a) * ∏ a, (f a).factorial := by
  rw [← Nat.multinomial_spec univ f, mul_comm]
  exact Nat.mul_le_mul_right _ (multinomial_le_pow f)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem monomial_factorization_lower : MonoFactLow := by
  intro N ν m hm
  classical
  have h1 : ∏ k ∈ m.support, (m k).factorial = ∏ s : Fin N, ∏ a : Fin N, (m (a, s)).factorial := by
    rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
      rw [Finsupp.mem_support_iff, not_not] at hk
      rw [hk, Nat.factorial_zero])]
    rw [Fintype.prod_prod_type, Finset.prod_comm]
  rw [h1, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun s _ => ?_
  have := col_fact_le (fun a => m (a, s))
  rwa [hm s] at this

end PI.SlopeSteps
