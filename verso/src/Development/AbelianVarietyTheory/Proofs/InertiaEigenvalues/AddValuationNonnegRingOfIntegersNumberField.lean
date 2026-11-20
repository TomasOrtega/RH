import Mathlib

open NumberField

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Consider separately whether the proposition holds or fails. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem addValuation_nonneg_of_ringOfIntegers :
    ∀ (L : Type) [Field L] [NumberField L] (v : AddValuation L (WithTop ℤ)) (a : 𝓞 L),
      0 ≤ v (a : L) := by
  intro L _ _ v a
  have hZ : ∀ m : ℤ, 0 ≤ v (m : L) := by
    intro m
    induction m using Int.induction_on with
    | zero => simp [AddValuation.map_zero]
    | succ k ih =>
      rw [Int.cast_add, Int.cast_one]
      exact AddValuation.map_le_add v ih (by rw [AddValuation.map_one])
    | pred k ih =>
      rw [Int.cast_sub, Int.cast_one]
      exact AddValuation.map_le_sub v ih (by rw [AddValuation.map_one])
  by_contra hneg
  push_neg at hneg
  obtain ⟨f, hm, hf⟩ := NumberField.RingOfIntegers.isIntegral_coe a
  set x : L := (a : L) with hx
  have hxtop : v x ≠ ⊤ := ne_top_of_lt hneg
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hxtop
  have hk0 : k < 0 := by
    rw [← hk] at hneg
    exact_mod_cast hneg
  by_cases hn : f.natDegree = 0
  · rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    have hc : c = 1 := by
      have h1 := hm.leadingCoeff
      rwa [Polynomial.leadingCoeff_C] at h1
    subst hc
    simp at hf
  simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
    one_mul, add_eq_zero_iff_eq_neg] at hf
  apply_fun v at hf
  rw [AddValuation.map_neg, AddValuation.map_pow, ← hk] at hf
  have hlt : ((f.natDegree • k : ℤ) : WithTop ℤ) <
      v (∑ i ∈ Finset.range f.natDegree, (algebraMap ℤ L) (f.coeff i) * x ^ i) := by
    apply AddValuation.map_lt_sum v (WithTop.coe_ne_top)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [AddValuation.map_mul, AddValuation.map_pow, ← hk, eq_intCast]
    calc ((f.natDegree • k : ℤ) : WithTop ℤ) < ((i • k : ℤ) : WithTop ℤ) := by
          rw [WithTop.coe_lt_coe, nsmul_eq_mul, nsmul_eq_mul]
          have : (i : ℤ) < f.natDegree := by exact_mod_cast hi
          nlinarith
      _ = i • (k : WithTop ℤ) := by rw [WithTop.coe_nsmul]
      _ ≤ v ((f.coeff i : ℤ) : L) + i • (k : WithTop ℤ) := le_add_of_nonneg_left (hZ _)
  rw [WithTop.coe_nsmul, hf] at hlt
  exact lt_irrefl _ hlt

end GlobalTheory
