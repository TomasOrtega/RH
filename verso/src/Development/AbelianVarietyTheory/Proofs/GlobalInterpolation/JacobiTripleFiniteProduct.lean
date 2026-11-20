import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QBinomialFiniteStatement
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Finset.sum_range_succ, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finTriple_sum_odd (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/- English proof (translation)
Establish `hc : finCoeff (s ^ 2) n ((k : ℤ) - n) = qBinom (s ^ 2) (2 * n) k`. Unfold `finCoeff`. Rewrite using `[if_pos (by omega)]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hc]`. Establish `hkk : ((k * (k - 1) : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) - 1)`. Break down `k with _ | k` into its components or cases. Simplify using the standard rewrite rules. Move the coercions through the operations in `[Nat.add_sub_cancel]`.

Expand and normalize the polynomial expressions, which then agree. Establish `he : ((k : ℤ) - n) ^ 2 = ((n ^ 2 + k * (k - 1) : ℕ) : ℤ) + (1 - 2 * n) * k`. Rewrite using `[Nat.cast_add, hkk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hxz : x ^ ((k : ℤ) - n) = x ^ k * x⁻¹ ^ n`. Rewrite using `[zpow_sub₀ hx, zpow_natCast, zpow_natCast, div_eq_mul_inv, inv_pow]`. Rewrite using `[hxz, he, zpow_add₀ hs, zpow_natCast, zpow_mul, zpow_natCast, pow_add, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
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
Use `set X := x * s ^ ((1 : ℤ) - 2 * n) with hX`. Establish `ha : ∀ k ∈ Finset.range n, 1 + x * s ^ (2 * k + 1) = 1 + X * s ^ (2 * (n + k))`. Introduce `k _`. Rewrite using `[hX, mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs]`. Use `congr 3`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : ∀ k ∈ Finset.range n, 1 + x⁻¹ * s ^ (2 * k + 1) = (x⁻¹ * s ^ (2 * k + 1)) * (1 + X * s ^ (2 * (n - 1 - k)))`. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_range]`.

Establish `e : ((2 * k + 1 : ℕ) : ℤ) + (1 - 2 * n) + ((2 * (n - 1 - k) : ℕ) : ℤ) = 0` using `by omega`. Establish `hab : x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k))) = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hX, zpow_natCast, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 1 := by`. Rewrite using `[inv_mul_cancel₀ hx, ← zpow_add₀ hs, ← zpow_add₀ hs, e, zpow_zero, one_mul]`. Take the linear combination `-hab`. Establish `hr : ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n - 1 - k))) = ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k))` using `Finset.prod_range_reflect (fun k => 1 + X * s ^ (2 * k)) n`. Establish `hC : ∏ k ∈ Finset.range n, (x⁻¹ * s ^ (2 * k + 1)) = x⁻¹ ^ n * s ^ (n ^ 2)`.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_pow_eq_pow_sum, finTriple_sum_odd]`. Establish `hsplit : ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) = (∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k))) * ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n + k)))`. Rewrite using `[two_mul, Finset.prod_range_add]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_congr rfl ha, Finset.prod_congr rfl hb, Finset.prod_mul_distrib, hr, hC]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hsplit]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = x⁻¹ ^ n * s ^ (n ^ 2) * ∑ k ∈ Finset.range (2 * n + 1), qBinom (s ^ 2) (2 * n) k * s ^ (k * (k - 1)) * X ^ k := by`. Rewrite using `[GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom s X hs1 (2 * n)]`. Use `_ = ∑ k ∈ Finset.range (2 * n + 1), finCoeff (s ^ 2) n ((k : ℤ) - n) * (x ^ ((k : ℤ) - n) * s ^ (((k : ℤ) - n) ^ 2)) := by`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun k hk => ?_)` and prove the remaining obligations. Rewrite `hk` using `[Finset.mem_range]`. Conclude with `finTriple_term s x hs hx n k (by omega)`. Use `_ = _ := by`.

Use `Finset.sum_nbij' (fun k : ℕ => (k : ℤ) - n) (fun j : ℤ => (j + n).toNat) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Simplify using `only [Finset.mem_coe, Finset.mem_range] at ha`. Simplify using `only [Finset.mem_coe, Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.

Introduce `a ha`. Simplify using `only [Finset.mem_coe, Finset.mem_Icc] at ha`. Simplify using `only [Finset.mem_coe, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Introduce `a _`.

Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [Finset.mem_coe, Finset.mem_Icc] at ha`. Use linear arithmetic over natural numbers and integers. Introduce `a _`.

Both sides reduce to the same expression.
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
