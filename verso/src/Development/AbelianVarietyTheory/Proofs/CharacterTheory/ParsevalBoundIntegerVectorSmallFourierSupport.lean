import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem parsevalSep_orth (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N) (k l : ℕ)
    (hk : k < N) (hl : l < N) :
    ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l)
      = if k = l then (N : ℂ) else 0 := by
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have h0 : ω ≠ 0 := hω.ne_zero hN.ne'
  rw [← Complex.inv_eq_conj h1]
  have hz : ∀ j : ℕ, ω ^ (j * k) * (ω⁻¹) ^ (j * l) = (ω ^ k * (ω ^ l)⁻¹) ^ j := by
    intro j
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l]
  simp_rw [hz]
  split_ifs with h
  · subst h
    simp [mul_inv_cancel₀ (pow_ne_zero k h0)]
  · have hne : ω ^ k * (ω ^ l)⁻¹ ≠ 1 := by
      intro h'
      apply h
      apply hω.pow_inj hk hl
      field_simp at h'
      exact h'
    have hp : (ω ^ k * (ω ^ l)⁻¹) ^ N = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l, pow_mul, pow_mul,
        hω.pow_eq_one]
      simp
    rw [geom_sum_eq hne, hp]
    simp

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Move the embeddings inside the algebraic operations. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem parsevalSep_identity (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N)
    (c : ℕ → ℤ) :
    ∑ j ∈ Finset.range N, ‖∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k)‖ ^ 2
      = (N : ℝ) * ((∑ k ∈ Finset.range N, c k ^ 2 : ℤ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, map_mul, map_pow, map_intCast]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  have : ∀ l ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l))
      = if k = l then (c k : ℂ) * c l * N else 0 := by
    intro l hl
    have := parsevalSep_orth N ω hN hω k l (Finset.mem_range.1 hk) (Finset.mem_range.1 hl)
    have e : ∑ j ∈ Finset.range N,
      (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l))
       = (c k : ℂ) * c l * ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, this]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hk]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem parsevalSep_bound : ∀ (n N : ℕ) (ω : ℂ) (c : ℕ → ℤ) (S : Finset ℕ), 0 < n → 0 < N → IsPrimitiveRoot ω N → ∑ k ∈ Finset.range N, c k ^ 2 = 2 * n → |∑ k ∈ Finset.range N, c k| ≤ (n : ℤ) - 1 → (∀ j : ℕ, 0 < j → j < N → j ∉ S → ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) = 0) → 2 * n * N ≤ (n - 1) ^ 2 + 4 * n ^ 2 * S.card := by
  intro n N ω c S hn hN hω h2 h0 hS
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have hP := parsevalSep_identity N ω hN hω c
  rw [h2] at hP
  set F : ℕ → ℂ := fun j => ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) with hF
  have hb : ∀ j, ‖F j‖ ≤ 2 * n := by
    intro j
    have h2' : ∑ k ∈ Finset.range N, (c k : ℝ) ^ 2 = 2 * n := by exact_mod_cast h2
    rw [← h2']
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow, h1, one_pow, mul_one, Complex.norm_intCast]
    have : |c k| ≤ c k ^ 2 := by
      rw [← sq_abs]
      have := abs_nonneg (c k)
      nlinarith [Int.le_self_sq |c k|]
    exact_mod_cast this
  have hz : ‖F 0‖ ≤ (n : ℝ) - 1 := by
    have : F 0 = ((∑ k ∈ Finset.range N, c k : ℤ) : ℂ) := by simp [hF]
    rw [this, Complex.norm_intCast]
    exact_mod_cast h0
  have hle : ∀ j ∈ Finset.range N, ‖F j‖ ^ 2 ≤
      (if j = 0 then ((n : ℝ) - 1) ^ 2 else 0) + (if j ∈ S then 4 * (n : ℝ) ^ 2 else 0) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      have : ‖F 0‖ ^ 2 ≤ ((n : ℝ) - 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      rw [if_pos rfl]
      split_ifs
      · have : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by positivity
        linarith
      · linarith
    · rw [if_neg hj0, zero_add]
      split_ifs with hjS
      · have := pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
        linarith [show (2 * (n : ℝ)) ^ 2 = 4 * (n : ℝ) ^ 2 by ring]
      · have : F j = 0 := hS j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj) hjS
        simp [this]
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hN),
    Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((Finset.range N ∩ S).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hP' : ∑ j ∈ Finset.range N, ‖F j‖ ^ 2 = (N : ℝ) * (2 * n) := by
    rw [hP]; push_cast; ring
  have key : (2 * n * N : ℝ) ≤ ((n : ℝ) - 1) ^ 2 + 4 * (n : ℝ) ^ 2 * S.card := by
    have : ((Finset.range N ∩ S).card : ℝ) * (4 * (n : ℝ) ^ 2) ≤ S.card * (4 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  rw [← hn1] at key
  exact_mod_cast key

end GlobalTheory
