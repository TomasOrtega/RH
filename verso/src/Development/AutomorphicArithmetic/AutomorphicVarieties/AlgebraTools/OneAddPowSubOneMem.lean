import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.AlgebraTools.prime_pow_dvd_choose (l : ℕ) (hl : l.Prime) (e j s : ℕ) (hj : j ≤ e)
    (hs : s + 1 < l ^ (e - j)) : l ^ j ∣ (l ^ e).choose (s + 1) := by
  have hm : s + 1 ≤ l ^ e :=
    le_of_lt (lt_of_lt_of_le hs (Nat.pow_le_pow_right hl.pos (Nat.sub_le e j)))
  have hC : (l ^ e).choose (s + 1) ≠ 0 := (Nat.choose_pos hm).ne'
  have hv : (s + 1).factorization l < e - j := by
    have h1 : l ^ (s + 1).factorization l ≤ s + 1 :=
      Nat.le_of_dvd (Nat.succ_pos s) (Nat.ordProj_dvd (s + 1) l)
    exact (Nat.pow_lt_pow_iff_right hl.one_lt).1 (lt_of_le_of_lt h1 hs)
  rw [hl.pow_dvd_iff_le_factorization hC, Nat.factorization_choose_prime_pow hl hm (Nat.succ_ne_zero s)]
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.one_add_pow_sub_one_mem :
    ∀ (R : Type) [CommRing R] (l : ℕ), l.Prime → ∀ (y : R) (e j k : ℕ), j ≤ e → k ≤ l ^ (e - j) →
      (1 + y) ^ l ^ e - 1 ∈ Ideal.span {y ^ k} ⊔ Ideal.span {(l : R) ^ j} := by
  intro R _ l hl y e j k hj hk
  have hN : (1 + y) ^ l ^ e - 1 =
      ∑ s ∈ Finset.range (l ^ e), y ^ (s + 1) * ((l ^ e).choose (s + 1) : R) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp
  rw [hN]
  refine Ideal.sum_mem _ fun s _ => ?_
  by_cases hks : k ≤ s + 1
  · apply Ideal.mem_sup_left
    rw [Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (pow_dvd_pow y hks) _
  · apply Ideal.mem_sup_right
    rw [Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.prime_pow_dvd_choose l hl e j s hj (by omega)
    exact ⟨y ^ (s + 1) * c, by rw [hc]; push_cast; ring⟩
