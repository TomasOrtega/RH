import Mathlib
open Real

namespace GlobalTheory

/- English proof (translation)
Establish `h2 : HasSum (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) (π^2/6)`. Use `(hasSum_nat_add_iff' 1).mpr hasSum_zeta_two` as an intermediate fact. Simplify using `using this`. Establish `hle : ∀ n : ℕ, (1:ℝ)/((n:ℝ)+1)^i ≤ 1/((n:ℝ)+1)^2`. Introduce `n`.

Establish `h1 : (1:ℝ) ≤ (n:ℝ)+1` using `by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]`. Apply `one_div_le_one_div_of_le (by positivity)` to reduce the goal to its premises. Conclude with `pow_le_pow_right₀ h1 hi`. Establish `hnn : ∀ n : ℕ, (0:ℝ) ≤ 1/((n:ℝ)+1)^i` using `fun n => by positivity`. Establish `hs : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^i)` using `Summable.of_nonneg_of_le hnn hle h2.summable`.

Combine the equalities or inequalities in the displayed calculation. Use `Real.pi_lt_d2` as an intermediate fact. Use `Real.pi_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem zetaTerm_tsum_le_two (i : ℕ) (hi : 2 ≤ i) :
    ∑' n : ℕ, 1/((n:ℝ)+1)^i ≤ 2 := by
  have h2 : HasSum (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) (π^2/6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hle : ∀ n : ℕ, (1:ℝ)/((n:ℝ)+1)^i ≤ 1/((n:ℝ)+1)^2 := by
    intro n
    have h1 : (1:ℝ) ≤ (n:ℝ)+1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ h1 hi
  have hnn : ∀ n : ℕ, (0:ℝ) ≤ 1/((n:ℝ)+1)^i := fun n => by positivity
  have hs : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^i) :=
    Summable.of_nonneg_of_le hnn hle h2.summable
  calc ∑' n : ℕ, 1/((n:ℝ)+1)^i ≤ ∑' n : ℕ, 1/((n:ℝ)+1)^2 := hs.tsum_le_tsum hle h2.summable
    _ = π^2/6 := h2.tsum_eq
    _ ≤ 2 := by
      have := Real.pi_lt_d2
      have := Real.pi_pos
      nlinarith

/- English proof (translation)
Establish `hprod : ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i) ≤ ∏ _i ∈ Finset.Icc 2 r, (2:ℝ)`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i _; exact tsum_nonneg (fun n => by positivity)`. Introduce `i hi`. Conclude with `zetaTerm_tsum_le_two i (Finset.mem_Icc.mp hi).1`.

Rewrite `hprod` using `[Finset.prod_const, Nat.card_Icc]`. Establish `hexp : r + 1 - 2 ≤ r*(r-1)/2`. Take `⟨k, rfl⟩ : ∃ k, r = k + 2` from `⟨r - 2, by omega⟩`. Rewrite using `[Nat.le_div_iff_mul_le (by norm_num)]`. Establish `: k + 2 + 1 - 2 = k + 1` using `by omega`.

Establish `h' : k + 2 - 1 = k + 1` using `by omega`. Rewrite using `[this, h']`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpow : (2:ℝ)^(r+1-2) ≤ 2^(r*(r-1)/2)` using `pow_le_pow_right₀ (by norm_num) hexp`. Establish `hpi : (1:ℝ) ≤ (2*π)^(r-1)` using `one_le_pow₀ (by linarith [Real.pi_gt_three])`.

Establish `hsq : 0 ≤ √(r:ℝ)` using `Real.sqrt_nonneg _`. Establish `h2p : (0:ℝ) ≤ 2^(r*(r-1)/2)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hsq` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Use `_ = 2^(r*(r-1)/2) * (2*π)^(r-1) * √r := by ring`.
-/
theorem volumeConstant_le (r : ℕ) (hr : 2 ≤ r) :
    √r * ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i) ≤ 2^(r*(r-1)/2) * (2*π)^(r-1) * √r := by
  have hprod : ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i) ≤ ∏ _i ∈ Finset.Icc 2 r, (2:ℝ) := by
    apply Finset.prod_le_prod
    · intro i _; exact tsum_nonneg (fun n => by positivity)
    · intro i hi; exact zetaTerm_tsum_le_two i (Finset.mem_Icc.mp hi).1
  rw [Finset.prod_const, Nat.card_Icc] at hprod
  have hexp : r + 1 - 2 ≤ r*(r-1)/2 := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : k + 2 + 1 - 2 = k + 1 := by omega
    have h' : k + 2 - 1 = k + 1 := by omega
    rw [this, h']
    nlinarith
  have hpow : (2:ℝ)^(r+1-2) ≤ 2^(r*(r-1)/2) := pow_le_pow_right₀ (by norm_num) hexp
  have hpi : (1:ℝ) ≤ (2*π)^(r-1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hsq : 0 ≤ √(r:ℝ) := Real.sqrt_nonneg _
  have h2p : (0:ℝ) ≤ 2^(r*(r-1)/2) := by positivity
  calc √r * ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i)
      ≤ √r * 2^(r*(r-1)/2) := mul_le_mul_of_nonneg_left (hprod.trans hpow) hsq
    _ ≤ √r * (2^(r*(r-1)/2) * (2*π)^(r-1)) := by
        apply mul_le_mul_of_nonneg_left _ hsq
        nlinarith
    _ = 2^(r*(r-1)/2) * (2*π)^(r-1) * √r := by ring

/- English proof (translation)
The claim follows from `volumeConstant_le`.
-/
example : ∀ r : ℕ, 2 ≤ r → √r * ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i) ≤ 2^(r*(r-1)/2) * (2*π)^(r-1) * √r :=
  volumeConstant_le

end GlobalTheory
