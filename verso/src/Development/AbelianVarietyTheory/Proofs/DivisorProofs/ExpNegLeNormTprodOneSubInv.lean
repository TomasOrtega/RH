import Mathlib
open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory

/- English proof (translation)
Establish `hlow : ∀ a, 1 / 2 ≤ ‖1 - x a‖`. Introduce `a`. Establish `h1` using `norm_sub_norm_le (1 : ℂ) (x a)`. Rewrite `h1` using `[norm_one]`. Combine the linear relations using `[h a]`.

Establish `hne : ∀ a, 1 - x a ≠ 0`. Introduce `a h0`. Use `hlow a` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `heq : ∀ a, (1 - x a)⁻¹ = 1 + x a * (1 - x a)⁻¹`. Introduce `a`. Use `hne a` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hsum : Summable (fun a => ‖x a * (1 - x a)⁻¹‖)`. Use `Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_) (hs.mul_right 2)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_inv]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[inv_le_comm₀ (by linarith [hlow a]) (by norm_num)]`.

Combine the linear relations using `[hlow a]`. Establish `hm : Multipliable (fun a => (1 - x a)⁻¹)`. Use `multipliable_one_add_of_summable hsum` as an intermediate fact. Simplify `this` using `only [← heq]`. Establish `hfac : ∀ a, Real.exp (-‖x a‖) ≤ ‖(1 - x a)⁻¹‖`.

Introduce `a`. Rewrite using `[norm_inv, Real.exp_neg]`. Use `inv_anti₀ (by linarith [hlow a]) ?_` and prove the remaining obligations. Establish `h1` using `norm_sub_le (1 : ℂ) (x a)`. Rewrite `h1` using `[norm_one]`.

Combine the linear relations using `[Real.add_one_le_exp ‖x a‖]`. Establish `ht` using `(continuous_norm.tendsto _).comp hm.hasProd`. Use `ge_of_tendsto' ht (fun s => ?_)` and prove the remaining obligations. Establish `hsle : ∑ a ∈ s, ‖x a‖ ≤ B` using `(hs.sum_le_tsum s (fun a _ => norm_nonneg _)).trans hB`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_neg_distrib]`. Conclude with `Real.exp_le_exp.2 (neg_le_neg hsle)`. Use `_ = ∏ a ∈ s, Real.exp (-‖x a‖) := Real.exp_sum _ _`. Use `_ ≤ ∏ a ∈ s, ‖(1 - x a)⁻¹‖ := Finset.prod_le_prod (fun a _ => (Real.exp_pos _).le) (fun a _ => hfac a)`. Use `_ = _ := by simp only [Function.comp, norm_prod]`.
-/
theorem exp_neg_le_norm_tprod_one_sub_inv {ι : Type} (x : ι → ℂ) (B : ℝ)
    (h : ∀ a, ‖x a‖ ≤ 1 / 2) (hs : Summable (fun a => ‖x a‖)) (hB : ∑' a, ‖x a‖ ≤ B) :
    Real.exp (-B) ≤ ‖∏' a, (1 - x a)⁻¹‖ := by
  have hlow : ∀ a, 1 / 2 ≤ ‖1 - x a‖ := by
    intro a
    have h1 := norm_sub_norm_le (1 : ℂ) (x a)
    rw [norm_one] at h1
    linarith [h a]
  have hne : ∀ a, 1 - x a ≠ 0 := by
    intro a h0
    have := hlow a
    rw [h0, norm_zero] at this
    linarith
  have heq : ∀ a, (1 - x a)⁻¹ = 1 + x a * (1 - x a)⁻¹ := by
    intro a
    have := hne a
    field_simp
    ring
  have hsum : Summable (fun a => ‖x a * (1 - x a)⁻¹‖) := by
    refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_) (hs.mul_right 2)
    rw [norm_mul, norm_inv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [inv_le_comm₀ (by linarith [hlow a]) (by norm_num)]
    linarith [hlow a]
  have hm : Multipliable (fun a => (1 - x a)⁻¹) := by
    have := multipliable_one_add_of_summable hsum
    simpa only [← heq] using this
  have hfac : ∀ a, Real.exp (-‖x a‖) ≤ ‖(1 - x a)⁻¹‖ := by
    intro a
    rw [norm_inv, Real.exp_neg]
    refine inv_anti₀ (by linarith [hlow a]) ?_
    have h1 := norm_sub_le (1 : ℂ) (x a)
    rw [norm_one] at h1
    linarith [Real.add_one_le_exp ‖x a‖]
  have ht := (continuous_norm.tendsto _).comp hm.hasProd
  refine ge_of_tendsto' ht (fun s => ?_)
  have hsle : ∑ a ∈ s, ‖x a‖ ≤ B :=
    (hs.sum_le_tsum s (fun a _ => norm_nonneg _)).trans hB
  calc Real.exp (-B) ≤ Real.exp (∑ a ∈ s, -‖x a‖) := by
        rw [Finset.sum_neg_distrib]
        exact Real.exp_le_exp.2 (neg_le_neg hsle)
    _ = ∏ a ∈ s, Real.exp (-‖x a‖) := Real.exp_sum _ _
    _ ≤ ∏ a ∈ s, ‖(1 - x a)⁻¹‖ :=
        Finset.prod_le_prod (fun a _ => (Real.exp_pos _).le) (fun a _ => hfac a)
    _ = _ := by simp only [Function.comp, norm_prod]

end GlobalTheory
