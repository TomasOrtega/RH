import Mathlib
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Establish `hq : ∀ x : Fin g → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Y *ᵥ x)`. Introduce `x`. Establish `h` using `hY.dotProduct_mulVec_nonneg x`. Simplify using `only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hdet : IsUnit Y.det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Take `⟨v, hv, hYv⟩` from `(Matrix.exists_mulVec_eq_zero_iff).2 h0`. Establish `h1` using `hq v`.

Rewrite `h1` using `[hYv, dotProduct_zero]`. Establish `h2 : v ⬝ᵥ v = 0` using `le_antisymm (by nlinarith [dotProduct_self_star_nonneg v]) (by`. Simplify using `using dotProduct_self_star_nonneg v)`. Conclude with `hv (by simpa using h2)`. Establish `hYinv : Y * Y⁻¹ = 1` using `Matrix.mul_nonsing_inv Y hdet`.

Establish `hmap : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[show Y.map Complex.ofReal = Y.map Complex.ofRealHom from rfl, show Y⁻¹.map Complex.ofReal = Y⁻¹.map Complex.ofRealHom from rfl, ← Matrix.map_mul, hYinv]`. Simplify using the standard rewrite rules. Rewrite using `[hmap, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]`.

Use `set w : Fin g → ℝ := Y⁻¹ *ᵥ Pi.single j 1 with hw`. Establish `hYw : Y *ᵥ w = Pi.single j 1`. Rewrite using `[hw, mulVec_mulVec, hYinv, one_mulVec]`. Establish `hwi : ∀ k, w k = Y⁻¹ k j`. Introduce `k`.

Simplify using `[hw, mulVec_single_one]`. Establish `hqw : c * (w ⬝ᵥ w) ≤ w j`. Use `hq w` as an intermediate fact. Rewrite `this` using `[hYw, dotProduct_single, mul_one]`. Conclude with `this`.

Establish `hsq : ∀ k, w k ^ 2 ≤ w ⬝ᵥ w`. Introduce `k`. Rewrite using `[dotProduct]`. Use `Finset.single_le_sum (f := fun l => w l * w l) (fun l _ => mul_self_nonneg (w l)) (Finset.mem_univ k)` as an intermediate fact. Simplify `this` using `[sq]`.

Establish `hj1` using `hsq j`. Establish `hi1` using `hsq i`. Establish `hwj0 : 0 ≤ w j` using `by nlinarith [sq_nonneg (w j)]`. Establish `hcwj : c * w j ≤ 1`. Break down `hwj0.lt_or_eq with h | h` into its components or cases.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[← h]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hci1 : c * w i ^ 2 ≤ w j` using `le_trans (mul_le_mul_of_nonneg_left hi1 hc.le) hqw`. Establish `hci : (c * w i) ^ 2 ≤ 1`.

Combine the equalities or inequalities in the displayed calculation. Establish `habs : |c * w i| ≤ 1` using `sq_le_one_iff_abs_le_one _ |>.1 hci`. Rewrite using `[← hwi i, le_div_iff₀ hc]`. Rewrite `habs` using `[abs_mul, abs_of_pos hc]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inv_entry_norm_le_of_sub_posSemidef (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ)
    (hc : 0 < c) (hY : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) (i j : Fin g) :
    ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by

  have hq : ∀ x : Fin g → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Y *ᵥ x) := by
    intro x
    have h := hY.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at h
    linarith

  have hdet : IsUnit Y.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hYv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have h1 := hq v
    rw [hYv, dotProduct_zero] at h1
    have h2 : v ⬝ᵥ v = 0 := le_antisymm (by nlinarith [dotProduct_self_star_nonneg v]) (by
      simpa using dotProduct_self_star_nonneg v)
    exact hv (by simpa using h2)
  have hYinv : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hdet

  have hmap : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
    apply Matrix.inv_eq_right_inv
    rw [show Y.map Complex.ofReal = Y.map Complex.ofRealHom from rfl,
      show Y⁻¹.map Complex.ofReal = Y⁻¹.map Complex.ofRealHom from rfl, ← Matrix.map_mul, hYinv]
    simp
  rw [hmap, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]

  set w : Fin g → ℝ := Y⁻¹ *ᵥ Pi.single j 1 with hw
  have hYw : Y *ᵥ w = Pi.single j 1 := by
    rw [hw, mulVec_mulVec, hYinv, one_mulVec]
  have hwi : ∀ k, w k = Y⁻¹ k j := by
    intro k; simp [hw, mulVec_single_one]
  have hqw : c * (w ⬝ᵥ w) ≤ w j := by
    have := hq w
    rw [hYw, dotProduct_single, mul_one] at this
    exact this
  have hsq : ∀ k, w k ^ 2 ≤ w ⬝ᵥ w := by
    intro k
    rw [dotProduct]
    have := Finset.single_le_sum (f := fun l => w l * w l) (fun l _ => mul_self_nonneg (w l))
      (Finset.mem_univ k)
    simpa [sq] using this
  have hj1 := hsq j
  have hi1 := hsq i
  have hwj0 : 0 ≤ w j := by nlinarith [sq_nonneg (w j)]
  have hcwj : c * w j ≤ 1 := by
    rcases hwj0.lt_or_eq with h | h
    · nlinarith
    · rw [← h]; linarith
  have hci1 : c * w i ^ 2 ≤ w j := le_trans (mul_le_mul_of_nonneg_left hi1 hc.le) hqw
  have hci : (c * w i) ^ 2 ≤ 1 := by
    calc (c * w i) ^ 2 = c * (c * w i ^ 2) := by ring
      _ ≤ c * w j := mul_le_mul_of_nonneg_left hci1 hc.le
      _ ≤ 1 := hcwj
  have habs : |c * w i| ≤ 1 := sq_le_one_iff_abs_le_one _ |>.1 hci
  rw [← hwi i, le_div_iff₀ hc]
  rw [abs_mul, abs_of_pos hc] at habs
  linarith

end GlobalTheory
