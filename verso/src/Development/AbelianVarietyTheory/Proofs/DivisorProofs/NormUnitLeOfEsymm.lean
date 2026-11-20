import Mathlib

namespace GlobalTheory.ElementarySymmetricNormBound

open Polynomial

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_esymm_eq_zero (s : Multiset ℂ) (x : ℂ) (hx : x ∈ s) :
    ∑ j ∈ Finset.range (Multiset.card s + 1),
      (-1) ^ j * (s.esymm j * x ^ (Multiset.card s - j)) = 0 := by
  have h := congrArg (Polynomial.eval x) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_finset_sum] at h
  simp only [Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_one] at h
  rw [← h]
  exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨x, hx, sub_self x⟩)

/- English proof (translation)
Establish an intermediate fact. Consider separately whether the proposition holds or fails. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_le_of_esymm (s : Multiset ℂ) (M : ℝ) (hM : 1 ≤ M)
    (h : ∀ j, 1 ≤ j → j ≤ Multiset.card s → ‖s.esymm j‖ ≤ M) (x : ℂ) (hx : x ∈ s) :
    ‖x‖ ≤ (Multiset.card s : ℝ) * M := by
  have hn1 : 1 ≤ Multiset.card s := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx⟩
  by_cases hx1 : ‖x‖ ≤ 1
  · calc ‖x‖ ≤ 1 := hx1
      _ ≤ M := hM
      _ ≤ (Multiset.card s : ℝ) * M :=
          le_mul_of_one_le_left (by linarith) (by exact_mod_cast hn1)
  push_neg at hx1
  have h0 := sum_esymm_eq_zero s x hx
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm]
  rw [Finset.sum_range_succ'] at h0
  simp only [pow_zero, he0, one_mul, Nat.sub_zero] at h0
  have hxn : x ^ Multiset.card s = -∑ i ∈ Finset.range (Multiset.card s),
      (-1) ^ (i + 1) * (s.esymm (i + 1) * x ^ (Multiset.card s - (i + 1))) :=
    eq_neg_of_add_eq_zero_right h0
  have hbound : ‖x‖ ^ Multiset.card s ≤
      (Multiset.card s : ℝ) * M * ‖x‖ ^ (Multiset.card s - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    calc _ ≤ ∑ i ∈ Finset.range (Multiset.card s),
          ‖(-1 : ℂ) ^ (i + 1) * (s.esymm (i + 1) * x ^ (Multiset.card s - (i + 1)))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (Multiset.card s), M * ‖x‖ ^ (Multiset.card s - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_range.mp hi
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact mul_le_mul (h (i + 1) (by omega) (by omega)) (pow_le_pow_right₀ hx1.le (by omega))
            (pow_nonneg (norm_nonneg _) _) (by linarith)
      _ = (Multiset.card s : ℝ) * M * ‖x‖ ^ (Multiset.card s - 1) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hpos : 0 < ‖x‖ ^ (Multiset.card s - 1) := pow_pos (by linarith) _
  have hsplit : ‖x‖ ^ Multiset.card s = ‖x‖ * ‖x‖ ^ (Multiset.card s - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit] at hbound
  exact le_of_mul_le_mul_right hbound hpos

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem norm_unit_le_of_esymm :
    ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), Multiset.card B = n → (1 : ℝ) ≤ M →
      (∀ (j : ℕ), (1 : ℕ) ≤ j → j ≤ n →
        ‖Multiset.esymm (Multiset.map (fun (b : ℂˣ) ↦ (↑b : ℂ)) B) j‖ ≤ M) →
      ∀ b ∈ B, ‖(↑b : ℂ)‖ ≤ (↑n : ℝ) * M := by
  intro n B M hcard hM h b hb
  have hb' := norm_le_of_esymm (B.map (fun b : ℂˣ => (b : ℂ))) M hM
    (fun j hj1 hj2 => by
      rw [Multiset.card_map, hcard] at hj2
      exact h j hj1 hj2) (b : ℂ) (Multiset.mem_map_of_mem _ hb)
  rwa [Multiset.card_map, hcard] at hb'

end GlobalTheory.ElementarySymmetricNormBound
