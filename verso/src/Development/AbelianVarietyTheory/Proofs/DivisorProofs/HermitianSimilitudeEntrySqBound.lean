import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `n P _hP hpos`. Consider the cases of `n with`. Consider the case `zero => exact ⟨0, fun _ _ _ _ i => i.elim0⟩`. Consider the case `succ k`. Use `set q : (Fin (k+1) → ℂ) → ℝ := fun x => (star x ⬝ᵥ P *ᵥ x).re with hq`.

Establish `hcont : Continuous q`. Simplify using `only [hq, dotProduct, mulVec, Pi.star_apply]`. Use `fun_prop`. Establish `hsmul : ∀ (t : ℝ) (x : Fin (k+1) → ℂ), q ((t : ℂ) • x) = t ^ 2 * q x`. Introduce `t x`.

Simplify using `only [hq, star_smul, Complex.star_def, Complex.conj_ofReal, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Rewrite using `[← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨x0, hx0S, hmin⟩` from `(isCompact_sphere (0 : Fin (k+1) → ℂ) 1).exists_isMinOn (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn`. Use `set m := q x0 with hm_def`.

Establish `hx0 : x0 ≠ 0`. Introduce `h`. Rewrite `hx0S` using `[h]`. Simplify using `at hx0S`. Establish `hm : 0 < m` using `hpos x0 hx0`.

Establish `hlow : ∀ x, m * ‖x‖ ^ 2 ≤ q x`. Introduce `x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using `[hq]`.

Establish `hn : 0 < ‖x‖` using `norm_pos_iff.mpr hx`. Use `set u : Fin (k+1) → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu`. Establish `huS : u ∈ Metric.sphere (0 : Fin (k+1) → ℂ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']`. Establish `hxu : x = ((‖x‖ : ℝ) : ℂ) • u`.

Rewrite using `[hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]`. Establish `h1 : m ≤ q u` using `hmin huS`. Establish `hqx : q x = ‖x‖ ^ 2 * q u` using `by conv_lhs => rw [hxu]`. Conclude with `hsmul _ _`. Rewrite using `[hqx]`.

Use polynomial arithmetic with `[sq_nonneg ‖x‖]`. Establish `hY : ∀ (Y : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) (s : ℝ), Yᴴ * P * Y = (s : ℂ) • P → ∀ x, q (Y *ᵥ x) = s * q x`. Introduce `Y s h x`. Simplify using `only [hq]`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]`.

Use `set C : ℝ := ∑ j, ‖P j j‖ with hC`. Use `⟨C / m, fun Y s hs h i j => ?_⟩` and prove the remaining obligations. Use `set e : Fin (k+1) → ℂ := Pi.single j 1 with he`. Establish `hYe : Y *ᵥ e = fun i => Y i j`. Rewrite using `[he, mulVec_single_one]`.

Both sides reduce to the same expression. Establish `hqe : q e = (P j j).re`. Simplify using `[hq, he, mulVec_single_one]`. Establish `hle : ‖Y i j‖ ≤ ‖Y *ᵥ e‖`. Rewrite using `[hYe]`.

Conclude with `norm_le_pi_norm (fun i => Y i j) i`. Establish `hPjj : (P j j).re ≤ C` using `(Complex.re_le_norm _).trans (Finset.single_le_sum (f := fun j => ‖P j j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j))`. Establish `key : m * ‖Y *ᵥ e‖ ^ 2 ≤ s * (P j j).re`. Rewrite using `[← hqe, ← hY Y s h e]`. Conclude with `hlow _`.

Establish `h2 : ‖Y i j‖ ^ 2 ≤ ‖Y *ᵥ e‖ ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hle 2`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hm]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hPjj hs.le]`.
-/
theorem herm_scale_entry_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian → (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) → ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P → ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s := by
  intro n P _hP hpos
  cases n with
  | zero => exact ⟨0, fun _ _ _ _ i => i.elim0⟩
  | succ k =>
  set q : (Fin (k+1) → ℂ) → ℝ := fun x => (star x ⬝ᵥ P *ᵥ x).re with hq
  have hcont : Continuous q := by
    simp only [hq, dotProduct, mulVec, Pi.star_apply]
    fun_prop
  have hsmul : ∀ (t : ℝ) (x : Fin (k+1) → ℂ), q ((t : ℂ) • x) = t ^ 2 * q x := by
    intro t x
    simp only [hq, star_smul, Complex.star_def, Complex.conj_ofReal, mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring
  obtain ⟨x0, hx0S, hmin⟩ := (isCompact_sphere (0 : Fin (k+1) → ℂ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
  set m := q x0 with hm_def
  have hx0 : x0 ≠ 0 := by
    intro h; rw [h] at hx0S; simp at hx0S
  have hm : 0 < m := hpos x0 hx0
  have hlow : ∀ x, m * ‖x‖ ^ 2 ≤ q x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [hq]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set u : Fin (k+1) → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
    have huS : u ∈ Metric.sphere (0 : Fin (k+1) → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hxu : x = ((‖x‖ : ℝ) : ℂ) • u := by
      rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
    have h1 : m ≤ q u := hmin huS
    have hqx : q x = ‖x‖ ^ 2 * q u := by
      conv_lhs => rw [hxu]
      exact hsmul _ _
    rw [hqx]
    nlinarith [sq_nonneg ‖x‖]
  have hY : ∀ (Y : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) (s : ℝ), Yᴴ * P * Y = (s : ℂ) • P →
      ∀ x, q (Y *ᵥ x) = s * q x := by
    intro Y s h x
    simp only [hq]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  set C : ℝ := ∑ j, ‖P j j‖ with hC
  refine ⟨C / m, fun Y s hs h i j => ?_⟩
  set e : Fin (k+1) → ℂ := Pi.single j 1 with he
  have hYe : Y *ᵥ e = fun i => Y i j := by
    rw [he, mulVec_single_one]; rfl
  have hqe : q e = (P j j).re := by
    simp [hq, he, mulVec_single_one]
  have hle : ‖Y i j‖ ≤ ‖Y *ᵥ e‖ := by
    rw [hYe]; exact norm_le_pi_norm (fun i => Y i j) i
  have hPjj : (P j j).re ≤ C :=
    (Complex.re_le_norm _).trans (Finset.single_le_sum (f := fun j => ‖P j j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j))
  have key : m * ‖Y *ᵥ e‖ ^ 2 ≤ s * (P j j).re := by
    rw [← hqe, ← hY Y s h e]; exact hlow _
  have h2 : ‖Y i j‖ ^ 2 ≤ ‖Y *ᵥ e‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith [mul_le_mul_of_nonneg_left hPjj hs.le]

end GlobalTheory
