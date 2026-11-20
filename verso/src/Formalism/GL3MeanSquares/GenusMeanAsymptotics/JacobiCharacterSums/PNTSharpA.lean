import Mathlib

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

/- English proof (translation)
Establish `hd : ∀ x ∈ Set.Icc (1 : ℝ) t, HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ ρ) (ρ * (x : ℂ) ^ (ρ - 1)) (Set.Icc 1 t) x`. Introduce `x hx`. Establish `hx0 : (0 : ℝ) < x` using `by linarith [hx.1]`. Conclude with `((Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).hasDerivWithinAt`. Establish `hb : ∀ x ∈ Set.Ico (1 : ℝ) t, ‖ρ * (x : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ‖`.

Introduce `x hx`. Establish `hx0 : (0 : ℝ) < x` using `by linarith [hx.1]`. Rewrite using `[norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]`. Establish `h1 : x ^ (ρ - 1).re ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx.1 (by simp; linarith)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h` using `norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩`. Simplify using `using h`.
-/
lemma sharp_cpow_sub_one {ρ : ℂ} (hρ0 : ρ ≠ 0) (hre : ρ.re ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t : ℂ) ^ ρ - 1‖ ≤ ‖ρ‖ * (t - 1) := by
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) t,
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ ρ) (ρ * (x : ℂ) ^ (ρ - 1)) (Set.Icc 1 t) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    exact ((Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) t, ‖ρ * (x : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ‖ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have h1 : x ^ (ρ - 1).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.1 (by simp; linarith)
    calc ‖ρ‖ * x ^ (ρ - 1).re ≤ ‖ρ‖ * 1 := by gcongr
      _ = ‖ρ‖ := mul_one _
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa using h

/- English proof (translation)
Establish `hρ1' : ρ - 1 ≠ 0` using `sub_ne_zero.2 hρ1`. Set `f : ℝ → ℂ` to `fun u => (((u : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) + (((u⁻¹ - 1 : ℝ)) : ℂ)`. Set `f' : ℝ → ℂ` to `fun u => ((u : ℂ) ^ ρ - 1) / (u : ℂ) ^ 2`. Establish `hd : ∀ x ∈ Set.Icc (1 : ℝ) (1 + δ), HasDerivWithinAt f (f' x) (Set.Icc 1 (1 + δ)) x`. Introduce `x hx`.

Establish `hx0 : (0 : ℝ) < x` using `by linarith [hx.1]`. Establish `hxc : (x : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hx0.ne'`. Establish `h1` using `(((Complex.hasStrictDerivAt_cpow_const (c := ρ - 1) (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).sub_const 1).div_const (ρ - 1)`. Establish `h2` using `((hasDerivAt_inv hx0.ne').sub_const 1).ofReal_comp`. Use `(h1.add h2).hasDerivWithinAt.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [f']`. Establish `e1 : (x : ℂ) ^ (ρ - 1 - 1) = (x : ℂ) ^ ρ / (x : ℂ) ^ 2`. Rewrite using `[show ρ - 1 - 1 = ρ - 2 by ring, Complex.cpow_sub _ _ hxc, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]`. Rewrite using `[e1]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hb : ∀ x ∈ Set.Ico (1 : ℝ) (1 + δ), ‖f' x‖ ≤ ‖ρ‖ * δ`. Introduce `x hx`. Establish `hx0 : (0 : ℝ) < x` using `by linarith [hx.1]`.

Establish `hk` using `sharp_cpow_sub_one hρ0 hre hx.1`. Simplify using `only [f']`. Rewrite using `[norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le]`. Establish `hx1 : 1 ≤ x ^ 2` using `one_le_pow₀ hx.1`. Combine the equalities or inequalities in the displayed calculation.

Establish `h` using `norm_image_sub_le_of_norm_deriv_le_segment' hd hb (1 + δ) ⟨by linarith, le_rfl⟩`. Establish `hf1 : f 1 = 0` using `by simp [f]`. Rewrite `h` using `[hf1, sub_zero, show 1 + δ - 1 = δ by ring]`. Conclude with `h`.
-/
lemma differenced_kernel_bound {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ‖(((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ)‖ ≤ ‖ρ‖ * δ * δ := by
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  let f : ℝ → ℂ := fun u => (((u : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) + (((u⁻¹ - 1 : ℝ)) : ℂ)
  let f' : ℝ → ℂ := fun u => ((u : ℂ) ^ ρ - 1) / (u : ℂ) ^ 2
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) (1 + δ), HasDerivWithinAt f (f' x) (Set.Icc 1 (1 + δ)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0.ne'
    have h1 := (((Complex.hasStrictDerivAt_cpow_const (c := ρ - 1)
      (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).sub_const 1).div_const (ρ - 1)
    have h2 := ((hasDerivAt_inv hx0.ne').sub_const 1).ofReal_comp
    refine (h1.add h2).hasDerivWithinAt.congr_deriv ?_
    simp only [f']
    have e1 : (x : ℂ) ^ (ρ - 1 - 1) = (x : ℂ) ^ ρ / (x : ℂ) ^ 2 := by
      rw [show ρ - 1 - 1 = ρ - 2 by ring, Complex.cpow_sub _ _ hxc,
        show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    rw [e1]
    push_cast
    field_simp
    ring
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) (1 + δ), ‖f' x‖ ≤ ‖ρ‖ * δ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hk := sharp_cpow_sub_one hρ0 hre hx.1
    simp only [f']
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    have hx1 : 1 ≤ x ^ 2 := one_le_pow₀ hx.1
    calc ‖(x : ℂ) ^ ρ - 1‖ / x ^ 2 ≤ ‖(x : ℂ) ^ ρ - 1‖ := div_le_self (norm_nonneg _) hx1
      _ ≤ ‖ρ‖ * (x - 1) := hk
      _ ≤ ‖ρ‖ * δ := by gcongr; linarith [hx.2]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (1 + δ) ⟨by linarith, le_rfl⟩
  have hf1 : f 1 = 0 := by simp [f]
  rw [hf1, sub_zero, show 1 + δ - 1 = δ by ring] at h
  exact h

/- English proof (translation)
Use `set g : ℂ := (((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) with hg`. Use `set e : ℂ := g + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ) with he`. Establish `hae` using `differenced_kernel_bound hρ0 hρ1 hre hδ`. Rewrite `hae` using `[← hg, ← he]`. Establish `hr : (1 + δ) / δ * ((1 + δ)⁻¹ - 1) = -1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hid : (((1 + δ) / δ : ℝ) : ℂ) * g - 1 = (((1 + δ) / δ : ℝ) : ℂ) * e`. Rewrite using `[he, mul_add, ← Complex.ofReal_mul, hr]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hq : 0 < (1 + δ) / δ` using `by positivity`. Rewrite using `[hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq.le]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma sharp_kernel {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖(((1 + δ) / δ : ℝ) : ℂ) * ((((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) - 1‖ ≤ 2 * δ * ‖ρ‖ := by
  set g : ℂ := (((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) with hg
  set e : ℂ := g + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ) with he
  have hae := differenced_kernel_bound hρ0 hρ1 hre hδ
  rw [← hg, ← he] at hae
  have hr : (1 + δ) / δ * ((1 + δ)⁻¹ - 1) = -1 := by
    field_simp
    ring
  have hid : (((1 + δ) / δ : ℝ) : ℂ) * g - 1 = (((1 + δ) / δ : ℝ) : ℂ) * e := by
    rw [he, mul_add, ← Complex.ofReal_mul, hr]
    push_cast
    ring
  have hq : 0 < (1 + δ) / δ := by positivity
  rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq.le]
  calc (1 + δ) / δ * ‖e‖ ≤ (1 + δ) / δ * (‖ρ‖ * δ * δ) := by gcongr
    _ = (1 + δ) * (δ * ‖ρ‖) := by field_simp
    _ ≤ 2 * (δ * ‖ρ‖) := by gcongr; linarith
    _ = 2 * δ * ‖ρ‖ := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
