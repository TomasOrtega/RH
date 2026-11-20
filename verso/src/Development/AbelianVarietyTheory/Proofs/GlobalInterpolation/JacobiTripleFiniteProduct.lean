import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QBinomialFiniteStatement
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finTriple_sum_odd (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finTriple_term (s x : ℂ) (hs : s ≠ 0) (hx : x ≠ 0) (n k : ℕ) (hk : k ≤ 2 * n) :
    (x⁻¹ ^ n * s ^ (n ^ 2)) *
        (qBinom (s ^ 2) (2 * n) k * s ^ (k * (k - 1)) * (x * s ^ ((1 : ℤ) - 2 * n)) ^ k) =
      finCoeff (s ^ 2) n ((k : ℤ) - n) * (x ^ ((k : ℤ) - n) * s ^ (((k : ℤ) - n) ^ 2)) := by
  have hc : finCoeff (s ^ 2) n ((k : ℤ) - n) = qBinom (s ^ 2) (2 * n) k := by
    unfold finCoeff
    rw [if_pos (by omega)]
    congr 1
    omega
  rw [hc]
  have hkk : ((k * (k - 1) : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
    rcases k with _ | k
    · simp
    · push_cast [Nat.add_sub_cancel]; ring
  have he : ((k : ℤ) - n) ^ 2 = ((n ^ 2 + k * (k - 1) : ℕ) : ℤ) + (1 - 2 * n) * k := by
    rw [Nat.cast_add, hkk]; push_cast; ring
  have hxz : x ^ ((k : ℤ) - n) = x ^ k * x⁻¹ ^ n := by
    rw [zpow_sub₀ hx, zpow_natCast, zpow_natCast, div_eq_mul_inv, inv_pow]
  rw [hxz, he, zpow_add₀ hs, zpow_natCast, zpow_mul, zpow_natCast, pow_add, mul_pow]
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Use linear arithmetic over natural numbers and integers.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem finTriple (s x : ℂ) (hs : s ≠ 0) (hs1 : ‖s‖ < 1) (hx : x ≠ 0) (n : ℕ) :
    ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) =
      ∑ j ∈ Finset.Icc (-(n : ℤ)) n, finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by
  set X := x * s ^ ((1 : ℤ) - 2 * n) with hX
  have ha : ∀ k ∈ Finset.range n, 1 + x * s ^ (2 * k + 1) = 1 + X * s ^ (2 * (n + k)) := by
    intro k _
    rw [hX, mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs]
    congr 3
    push_cast; ring
  have hb : ∀ k ∈ Finset.range n, 1 + x⁻¹ * s ^ (2 * k + 1) =
      (x⁻¹ * s ^ (2 * k + 1)) * (1 + X * s ^ (2 * (n - 1 - k))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e : ((2 * k + 1 : ℕ) : ℤ) + (1 - 2 * n) + ((2 * (n - 1 - k) : ℕ) : ℤ) = 0 := by omega
    have hab : x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k))) = 1 := by
      calc x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k)))
          = (x⁻¹ * x) * (s ^ ((2 * k + 1 : ℕ) : ℤ) * s ^ ((1 : ℤ) - 2 * n) *
              s ^ ((2 * (n - 1 - k) : ℕ) : ℤ)) := by
            rw [hX, zpow_natCast, zpow_natCast]; ring
        _ = 1 := by
            rw [inv_mul_cancel₀ hx, ← zpow_add₀ hs, ← zpow_add₀ hs, e, zpow_zero, one_mul]
    linear_combination -hab
  have hr : ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n - 1 - k))) =
      ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k)) :=
    Finset.prod_range_reflect (fun k => 1 + X * s ^ (2 * k)) n
  have hC : ∏ k ∈ Finset.range n, (x⁻¹ * s ^ (2 * k + 1)) = x⁻¹ ^ n * s ^ (n ^ 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, finTriple_sum_odd]
  have hsplit : ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) =
      (∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k))) *
        ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n + k))) := by
    rw [two_mul, Finset.prod_range_add]
  rw [Finset.prod_mul_distrib, Finset.prod_congr rfl ha, Finset.prod_congr rfl hb,
    Finset.prod_mul_distrib, hr, hC]
  calc _ = x⁻¹ ^ n * s ^ (n ^ 2) * ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) := by
        rw [hsplit]; ring
    _ = x⁻¹ ^ n * s ^ (n ^ 2) * ∑ k ∈ Finset.range (2 * n + 1),
          qBinom (s ^ 2) (2 * n) k * s ^ (k * (k - 1)) * X ^ k := by
        rw [GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom s X hs1 (2 * n)]
    _ = ∑ k ∈ Finset.range (2 * n + 1),
          finCoeff (s ^ 2) n ((k : ℤ) - n) * (x ^ ((k : ℤ) - n) * s ^ (((k : ℤ) - n) ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        exact finTriple_term s x hs hx n k (by omega)
    _ = _ := by
        refine Finset.sum_nbij' (fun k : ℕ => (k : ℤ) - n) (fun j : ℤ => (j + n).toNat)
          ?_ ?_ ?_ ?_ ?_
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_range] at ha
          simp only [Finset.mem_coe, Finset.mem_Icc]; omega
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_Icc] at ha
          simp only [Finset.mem_coe, Finset.mem_range]; omega
        · intro a _; omega
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_Icc] at ha
          omega
        · intro a _; rfl

end GlobalTheory.JacobiTriple
