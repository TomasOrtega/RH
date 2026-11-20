import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Establish `hq : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ∃ τ : ℍ, qm 1 τ = x`. Introduce `x hx0 hx1`. Establish `hx : x ≠ 0` using `norm_pos_iff.mp hx0`. Use `⟨⟨Function.Periodic.invQParam 1 x, Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hx1 hx⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `Function.Periodic.qParam_right_inv one_ne_zero hx`.

Unfold `Function.Periodic.qParam at h1`. Unfold `qm`. Simplify using `using h1`. Establish `hsum : ∀ τ : ℍ, HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ)` using `fun τ => hf.hasSum τ`. Establish `hconv : Conv (qExpansion 1 f)`.

Introduce `x hx`. Take `⟨y, hy⟩ : ∃ y : ℝ, y = (‖x‖ + 1) / 2` from `⟨_, rfl⟩`. Establish `hy0 : 0 < y` using `by rw [hy]; positivity`. Establish `hy1 : y < 1` using `by linarith`. Establish `hxy : ‖x‖ < y` using `by linarith`.

Establish `hyn : ‖(y : ℂ)‖ = y`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]`. Take `⟨τ, hτ⟩` from `hq (y : ℂ) (by rw [hyn]; exact hy0) (by rw [hyn]; exact hy1)`. Establish `hs` using `hsum τ`. Rewrite `hs` using `[hτ]`.

Establish `ht : Filter.Tendsto (fun n => ‖PowerSeries.coeff n (qExpansion 1 f) * (y : ℂ) ^ n‖) Filter.atTop (nhds 0)`. Simplify using `using hs.summable.tendsto_atTop_zero.norm`. Take `⟨C, hC⟩` from `ht.bddAbove_range`. Establish `hr0 : 0 ≤ ‖x‖ / y` using `by positivity`. Establish `hr1 : ‖x‖ / y < 1` using `(div_lt_one hy0).mpr hxy`.

Use `Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((summable_geometric_of_lt_one hr0 hr1).mul_left C)` and prove the remaining obligations. Establish `hb` using `hC ⟨n, rfl⟩`. Establish `he : ‖PowerSeries.coeff n (qExpansion 1 f)‖ * ‖x‖ ^ n = ‖PowerSeries.coeff n (qExpansion 1 f) * (y : ℂ) ^ n‖ * (‖x‖ / y) ^ n`. Rewrite using `[norm_mul, norm_pow, hyn, div_pow]`. Apply the tactic sequence `field_simp <;> ring`.

Rewrite using `[he]`. Conclude with `mul_le_mul_of_nonneg_right hb (by positivity)`. Use `eq_of_ev_eq hconv hs fun x hx0 hx1 => ?_` and prove the remaining obligations. Take `⟨τ, rfl⟩` from `hq x hx0 hx1`. Rewrite using `[h τ]`.

Conclude with `(hsum τ).tsum_eq`.
-/
theorem IsMF.qExp_eq {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) {s : PowerSeries ℂ} (hs : Conv s)
    (h : ∀ τ, ev s (qm 1 τ) = f τ) : qExpansion 1 f = s := by
  have hq : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ∃ τ : ℍ, qm 1 τ = x := by
    intro x hx0 hx1
    have hx : x ≠ 0 := norm_pos_iff.mp hx0
    refine ⟨⟨Function.Periodic.invQParam 1 x,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hx1 hx⟩, ?_⟩
    have h1 := Function.Periodic.qParam_right_inv one_ne_zero hx
    unfold Function.Periodic.qParam at h1
    unfold qm
    simpa using h1
  have hsum : ∀ τ : ℍ, HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ) :=
    fun τ => hf.hasSum τ
  have hconv : Conv (qExpansion 1 f) := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (‖x‖ + 1) / 2 := ⟨_, rfl⟩
    have hy0 : 0 < y := by rw [hy]; positivity
    have hy1 : y < 1 := by linarith
    have hxy : ‖x‖ < y := by linarith
    have hyn : ‖(y : ℂ)‖ = y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    obtain ⟨τ, hτ⟩ := hq (y : ℂ) (by rw [hyn]; exact hy0) (by rw [hyn]; exact hy1)
    have hs := hsum τ
    rw [hτ] at hs
    have ht : Filter.Tendsto (fun n => ‖PowerSeries.coeff n (qExpansion 1 f) * (y : ℂ) ^ n‖)
        Filter.atTop (nhds 0) := by
      simpa using hs.summable.tendsto_atTop_zero.norm
    obtain ⟨C, hC⟩ := ht.bddAbove_range
    have hr0 : 0 ≤ ‖x‖ / y := by positivity
    have hr1 : ‖x‖ / y < 1 := (div_lt_one hy0).mpr hxy
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
    have hb := hC ⟨n, rfl⟩
    have he : ‖PowerSeries.coeff n (qExpansion 1 f)‖ * ‖x‖ ^ n =
        ‖PowerSeries.coeff n (qExpansion 1 f) * (y : ℂ) ^ n‖ * (‖x‖ / y) ^ n := by
      rw [norm_mul, norm_pow, hyn, div_pow]
      field_simp <;> ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  refine eq_of_ev_eq hconv hs fun x hx0 hx1 => ?_
  obtain ⟨τ, rfl⟩ := hq x hx0 hx1
  rw [h τ]
  exact (hsum τ).tsum_eq

end ReciprocityTheory.ChartRestriction.L1
