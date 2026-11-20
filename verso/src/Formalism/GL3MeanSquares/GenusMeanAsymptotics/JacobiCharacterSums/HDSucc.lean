import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TpCoeffNorm

open Finset Complex Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

def hD (φ : ℕ → ℂ) (x : ℂ) (b : ℕ) : ℂ := ∑ a ∈ range (b + 1), φ a * x ^ (b - a)

/- English proof (translation)
Unfold `hD`. Rewrite using `[sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_sum]`. Use `congr 1`. Use `sum_congr rfl (fun a ha => ?_)` and prove the remaining obligations. Establish `: a ≤ b` using `Nat.lt_succ_iff.mp (mem_range.mp ha)`.

Rewrite using `[show b + 1 - a = (b - a) + 1 by omega, pow_succ]; ring`.
-/
theorem hD_succ (φ : ℕ → ℂ) (x : ℂ) (b : ℕ) : hD φ x (b + 1) = x * hD φ x b + φ (b + 1) := by
  unfold hD
  rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl (fun a ha => ?_)
  have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rw [show b + 1 - a = (b - a) + 1 by omega, pow_succ]; ring

/- English proof (translation)
Proceed by induction on `K with`. Consider the case `zero => simp [hD]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ K ih`. Rewrite using `[sum_range_succ (fun b => hD φ x b * ζ ^ b) (K + 1), mul_add, ih, sum_range_succ (fun b => φ b * ζ ^ b) (K + 1), hD_succ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hD_tele (φ : ℕ → ℂ) (x ζ : ℂ) (K : ℕ) :
    (1 - x * ζ) * ∑ b ∈ range (K + 1), hD φ x b * ζ ^ b =
      ∑ b ∈ range (K + 1), φ b * ζ ^ b - x * hD φ x K * ζ ^ (K + 1) := by
  induction K with
  | zero => simp [hD]; ring
  | succ K ih =>
    rw [sum_range_succ (fun b => hD φ x b * ζ ^ b) (K + 1), mul_add, ih,
      sum_range_succ (fun b => φ b * ζ ^ b) (K + 1), hD_succ]; ring

/- English proof (translation)
Use `set φ : ℕ → ℂ := fun a => (tp n z).coeff (n - a) with hφ`. Establish `hζ0 : ζ ≠ 0` using `by intro h; rw [h, norm_zero] at hζ1; linarith`. Establish `hβ0 : 0 ≤ β` using `(norm_nonneg _).trans (hβ (m + 1) le_rfl (by omega))`. Establish `hDn : ∀ x, hD φ x n = ∑ a ∈ range (n + 1), (tp n z).coeff a * x ^ a`. Introduce `x`.

Unfold `hD`. Rewrite using `[← Finset.sum_range_reflect (fun a => (tp n z).coeff a * x ^ a) (n + 1)]`. Use `sum_congr rfl (fun j hj => ?_)` and prove the remaining obligations. Establish `: j ≤ n` using `Nat.lt_succ_iff.mp (mem_range.mp hj)`. Simplify using `only [hφ]`.

Rewrite using `[show n + 1 - 1 - j = n - j by omega]`. Establish `hrefl : ∑ b ∈ range (n + 1), φ b * ζ ^ b = ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a)`. Rewrite using `[← Finset.sum_range_reflect (fun a => (tp n z).coeff a * ζ ^ (n - a)) (n + 1)]`. Use `sum_congr rfl (fun j hj => ?_)` and prove the remaining obligations. Establish `: j ≤ n` using `Nat.lt_succ_iff.mp (mem_range.mp hj)`.

Simplify using `only [hφ]`. Rewrite using `[show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]`. Establish `perI : ∀ i, (1 - z i * ζ) * ∑ b ∈ range n, hD φ (z i) b * ζ ^ b = ∏ l, (1 - z l * ζ)`. Introduce `i`. Establish `e1` using `hD_tele φ (z i) ζ (n - 1)`.

Rewrite `e1` using `[show n - 1 + 1 = n by omega]`. Rewrite using `[e1]`. Establish `hs` using `hD_succ φ (z i) (n - 1)`. Rewrite `hs` using `[show n - 1 + 1 = n by omega, hDn (z i), tp_root n z i]`. Rewrite using `[tp_rev n z ζ hζ0, ← hrefl, sum_range_succ]`.

Take the linear combination `ζ ^ n * hs`. Establish `perT : ∀ i, (∏ l, (1 - z l * ζ)) * ((z i * ζ) ^ (m + 1) / (1 - z i * ζ)) = ∑ b ∈ range n, ∑ a ∈ range (b + 1), ζ ^ (m + 1) * (ζ ^ b * (φ a * z i ^ (m + 1 + b - a)))`. Introduce `i`. Rewrite using `[← perI i]`. Establish `: (1 - z i * ζ) * (∑ b ∈ range n, hD φ (z i) b * ζ ^ b) * ((z i * ζ) ^ (m + 1) / (1 - z i * ζ)) = (z i * ζ) ^ (m + 1) * ∑ b ∈ range n, hD φ (z i) b * ζ ^ b`.

Clear denominators, using `[hne i]` for the nonvanishing conditions. Rewrite using `[this]`. Unfold `hD`. Simplify using `only [mul_sum, sum_mul]`. Use `sum_congr rfl (fun b _ => sum_congr rfl (fun a ha => ?_))` and prove the remaining obligations.

Establish `: a ≤ b` using `Nat.lt_succ_iff.mp (mem_range.mp ha)`. Rewrite using `[show m + 1 + b - a = (m + 1) + (b - a) by omega, pow_add, mul_pow]; ring`. Establish `key : (∏ l, (1 - z l * ζ)) * ∑ i, (z i * ζ) ^ (m + 1) / (1 - z i * ζ) = ζ ^ (m + 1) * ∑ b ∈ range n, ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)`. Rewrite using `[mul_sum, sum_congr rfl (fun i _ => perT i)]`. Simplify using `only [mul_sum]`.

Rewrite using `[sum_comm]`. Use `sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[sum_comm]`. Establish `hφsum : ∑ a ∈ range (n + 1), ‖φ a‖ ≤ 2 ^ n`. Establish `: ∑ a ∈ range (n + 1), ‖φ a‖ = ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖`.

Rewrite using `[← Finset.sum_range_reflect (fun a => ‖(tp n z).coeff a‖) (n + 1)]`. Use `sum_congr rfl (fun j hj => ?_)` and prove the remaining obligations. Simplify using `only [hφ]`. Rewrite using `[show n + 1 - 1 - j = n - j by omega]`. Rewrite using `[this]`.

Conclude with `tp_sum_norm n z hz`. Rewrite using `[← norm_mul, key, norm_mul, norm_pow]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation. Use `sum_le_sum (fun b hb => ?_)` and prove the remaining obligations.

Establish `hbn : b < n` using `mem_range.mp hb`. Rewrite using `[norm_mul, norm_pow]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation. Use `sum_le_sum (fun a ha => ?_)` and prove the remaining obligations.

Establish `: a ≤ b` using `Nat.lt_succ_iff.mp (mem_range.mp ha)`. Rewrite using `[norm_mul]`. Use `gcongr`. Conclude with `hβ _ (by omega) (by omega)`. Use `_ ≤ ∑ a ∈ range (n + 1), ‖φ a‖ * β := by`.

Apply `sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Conclude with `range_subset_range.mpr (by omega)`. Introduce `a _ _`. Check the signs of the components of the expression. Use `_ = (∑ a ∈ range (n + 1), ‖φ a‖) * β := by rw [sum_mul]`.

Use `_ ≤ 2 ^ n * β := by gcongr`. Use `_ = n * (‖ζ‖ ^ n * (2 ^ n * β)) := by rw [sum_const, card_range, nsmul_eq_mul]`.
-/
theorem Tbound (n m : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (β : ℝ)
    (hβ : ∀ k, m + 1 ≤ k → k ≤ m + n → ‖∑ i, z i ^ k‖ ≤ β) (ζ : ℂ) (hζ1 : 1 ≤ ‖ζ‖)
    (hne : ∀ i, 1 - z i * ζ ≠ 0) :
    ‖∏ i, (1 - z i * ζ)‖ * ‖∑ i, (z i * ζ) ^ (m + 1) / (1 - z i * ζ)‖ ≤
      ‖ζ‖ ^ (m + 1) * (n * (‖ζ‖ ^ n * (2 ^ n * β))) := by
  set φ : ℕ → ℂ := fun a => (tp n z).coeff (n - a) with hφ
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ1; linarith
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ (m + 1) le_rfl (by omega))
  have hDn : ∀ x, hD φ x n = ∑ a ∈ range (n + 1), (tp n z).coeff a * x ^ a := by
    intro x
    unfold hD
    rw [← Finset.sum_range_reflect (fun a => (tp n z).coeff a * x ^ a) (n + 1)]
    refine sum_congr rfl (fun j hj => ?_)
    have : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [hφ]
    rw [show n + 1 - 1 - j = n - j by omega]
  have hrefl : ∑ b ∈ range (n + 1), φ b * ζ ^ b =
      ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a) := by
    rw [← Finset.sum_range_reflect (fun a => (tp n z).coeff a * ζ ^ (n - a)) (n + 1)]
    refine sum_congr rfl (fun j hj => ?_)
    have : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [hφ]
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]
  have perI : ∀ i, (1 - z i * ζ) * ∑ b ∈ range n, hD φ (z i) b * ζ ^ b = ∏ l, (1 - z l * ζ) := by
    intro i
    have e1 := hD_tele φ (z i) ζ (n - 1)
    rw [show n - 1 + 1 = n by omega] at e1
    rw [e1]
    have hs := hD_succ φ (z i) (n - 1)
    rw [show n - 1 + 1 = n by omega, hDn (z i), tp_root n z i] at hs
    rw [tp_rev n z ζ hζ0, ← hrefl, sum_range_succ]
    linear_combination ζ ^ n * hs
  have perT : ∀ i, (∏ l, (1 - z l * ζ)) * ((z i * ζ) ^ (m + 1) / (1 - z i * ζ)) =
      ∑ b ∈ range n, ∑ a ∈ range (b + 1), ζ ^ (m + 1) * (ζ ^ b * (φ a * z i ^ (m + 1 + b - a))) := by
    intro i
    rw [← perI i]
    have : (1 - z i * ζ) * (∑ b ∈ range n, hD φ (z i) b * ζ ^ b) * ((z i * ζ) ^ (m + 1) / (1 - z i * ζ)) =
        (z i * ζ) ^ (m + 1) * ∑ b ∈ range n, hD φ (z i) b * ζ ^ b := by
      field_simp [hne i]
    rw [this]
    unfold hD
    simp only [mul_sum, sum_mul]
    refine sum_congr rfl (fun b _ => sum_congr rfl (fun a ha => ?_))
    have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
    rw [show m + 1 + b - a = (m + 1) + (b - a) by omega, pow_add, mul_pow]; ring
  have key : (∏ l, (1 - z l * ζ)) * ∑ i, (z i * ζ) ^ (m + 1) / (1 - z i * ζ) =
      ζ ^ (m + 1) * ∑ b ∈ range n, ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a) := by
    rw [mul_sum, sum_congr rfl (fun i _ => perT i)]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun b _ => ?_)
    rw [sum_comm]
  have hφsum : ∑ a ∈ range (n + 1), ‖φ a‖ ≤ 2 ^ n := by
    have : ∑ a ∈ range (n + 1), ‖φ a‖ = ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ := by
      rw [← Finset.sum_range_reflect (fun a => ‖(tp n z).coeff a‖) (n + 1)]
      refine sum_congr rfl (fun j hj => ?_)
      simp only [hφ]
      rw [show n + 1 - 1 - j = n - j by omega]
    rw [this]; exact tp_sum_norm n z hz
  rw [← norm_mul, key, norm_mul, norm_pow]
  gcongr
  calc ‖∑ b ∈ range n, ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖
      ≤ ∑ b ∈ range n, ‖ζ ^ b * ∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ range n, ‖ζ‖ ^ n * (2 ^ n * β) := by
        refine sum_le_sum (fun b hb => ?_)
        have hbn : b < n := mem_range.mp hb
        rw [norm_mul, norm_pow]
        gcongr
        calc ‖∑ a ∈ range (b + 1), φ a * ∑ i, z i ^ (m + 1 + b - a)‖
            ≤ ∑ a ∈ range (b + 1), ‖φ a * ∑ i, z i ^ (m + 1 + b - a)‖ := norm_sum_le _ _
          _ ≤ ∑ a ∈ range (b + 1), ‖φ a‖ * β := by
              refine sum_le_sum (fun a ha => ?_)
              have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
              rw [norm_mul]
              gcongr
              exact hβ _ (by omega) (by omega)
          _ ≤ ∑ a ∈ range (n + 1), ‖φ a‖ * β := by
              apply sum_le_sum_of_subset_of_nonneg
              · exact range_subset_range.mpr (by omega)
              · intro a _ _; positivity
          _ = (∑ a ∈ range (n + 1), ‖φ a‖) * β := by rw [sum_mul]
          _ ≤ 2 ^ n * β := by gcongr
    _ = n * (‖ζ‖ ^ n * (2 ^ n * β)) := by rw [sum_const, card_range, nsmul_eq_mul]

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
