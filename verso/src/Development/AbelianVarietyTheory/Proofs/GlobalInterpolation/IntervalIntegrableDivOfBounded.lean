import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

open MeasureTheory in
/- English proof (translation)
Establish `h : (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) = (fun n : ℕ => ‖∑ p ∈ (Finset.Ioc ⌊x⌋₊ n).filter Nat.Prime, a p‖) ∘ Nat.floor`. Use function extensionality and compare the values at `t`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `measurable_from_nat.comp Nat.measurable_floor`.
-/
private lemma measurable_norm_sum_primesIoc (a : ℕ → ℂ) (x : ℝ) :
    Measurable (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) := by
  have h : (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) =
      (fun n : ℕ => ‖∑ p ∈ (Finset.Ioc ⌊x⌋₊ n).filter Nat.Prime, a p‖) ∘ Nat.floor := by
    funext t
    rfl
  rw [h]
  exact measurable_from_nat.comp Nat.measurable_floor

open MeasureTheory in
/- English proof (translation)
Use `(norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _))` and prove the remaining obligations. Introduce `n hn`. Establish `hn'` using `(Finset.mem_filter.1 hn).1`. Establish `h1` using `(Finset.mem_Ioc.1 hn').2`. Establish `h2 : ⌊t⌋₊ ≤ ⌊y⌋₊` using `Nat.floor_le_floor hty`.

Conclude with `Finset.mem_range.2 (by omega)`.
-/
private lemma norm_sum_primesIoc_le_sum_range (a : ℕ → ℂ) (x y t : ℝ) (hty : t ≤ y) :
    ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ≤ ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ‖a n‖ := by
  refine (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _))
  intro n hn
  have hn' := (Finset.mem_filter.1 hn).1
  have h1 := (Finset.mem_Ioc.1 hn').2
  have h2 : ⌊t⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hty
  exact Finset.mem_range.2 (by omega)

open MeasureTheory in
/- English proof (translation)
Use `set B := ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ‖a n‖`. Use `Measure.integrableOn_of_bounded (M := B ^ k / x) (by simp) (((measurable_norm_sum_primesIoc a x).pow_const k).div measurable_id).aestronglyMeasurable ?_` and prove the remaining obligations. Use `ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)` and prove the remaining obligations. Establish `ht0 : 0 < t` using `hx.trans_le ht.1`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`.

Conclude with `div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_primesIoc_le_sum_range a x y t ht.2) k) hx ht.1`.
-/
private lemma integrableOn_norm_sum_primesIoc_pow_div (a : ℕ → ℂ) (x y : ℝ) (hx : 0 < x)
    (k : ℕ) :
    IntegrableOn (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ k / t) (Set.Icc x y) := by
  set B := ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ‖a n‖
  refine Measure.integrableOn_of_bounded (M := B ^ k / x) (by simp)
    (((measurable_norm_sum_primesIoc a x).pow_const k).div measurable_id).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
  have ht0 : 0 < t := hx.trans_le ht.1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_div₀ (by positivity)
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_primesIoc_le_sum_range a x y t ht.2) k) hx ht.1

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hI : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ k / t) volume x y`. Introduce `k`. Use `IntegrableOn.intervalIntegrable ?_` and prove the remaining obligations. Rewrite using `[Set.uIcc_of_le hxy]`.

Conclude with `integrableOn_norm_sum_primesIoc_pow_div a x y hx0 k`. Establish `hI1 : IntervalIntegrable (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) volume x y`. Simplify `hI 1` using `only [pow_one]`. Establish `hI0 : IntervalIntegrable (fun t : ℝ => 1 / t) volume x y`. Use `ContinuousOn.intervalIntegrable ?_` and prove the remaining obligations.

Use `continuousOn_const.div continuousOn_id (fun t ht => ?_)` and prove the remaining obligations. Rewrite `ht` using `[Set.uIcc_of_le hxy]`. Conclude with `(hx0.trans_le ht.1).ne'`. Establish `hlog : ∫ t in x..y, 1 / t = Real.log (y / x)` using `integral_one_div_of_pos hx0 (by linarith)`. Establish `hquad : ∀ c : ℝ, 0 ≤ Real.log (y / x) * (c * c) + (-2 * ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) * c + ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t`.

Introduce `c`. Establish `h0 : 0 ≤ ∫ t in x..y, (c - ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) ^ 2 / t` using `intervalIntegral.integral_nonneg hxy (fun t ht => div_nonneg (sq_nonneg _) (hx0.trans_le ht.1).le)`. Establish `heq : ∫ t in x..y, (c - ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) ^ 2 / t = (c * c) * (∫ t in x..y, 1 / t) - (2 * c) * (∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) + ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t`. Rewrite using `[← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hI0.const_mul _) (hI1.const_mul _), ← intervalIntegral.integral_add ((hI0.const_mul _).sub (hI1.const_mul _)) (hI 2)]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h0` using `[heq, hlog]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd` using `discrim_le_zero hquad`.

Unfold `discrim at hd`. Use polynomial arithmetic with `[hd]`.
-/
theorem _root_.GlobalTheory.Lin.sq_integral_primeSum_div_le (a : ℕ → ℂ) (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) ^ 2 ≤
      Real.log (y / x) * ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t := by
  have hx0 : 0 < x := by linarith
  have hI : ∀ k : ℕ, IntervalIntegrable
      (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ k / t) volume x y := by
    intro k
    refine IntegrableOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxy]
    exact integrableOn_norm_sum_primesIoc_pow_div a x y hx0 k
  have hI1 : IntervalIntegrable
      (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) volume x y := by
    simpa only [pow_one] using hI 1
  have hI0 : IntervalIntegrable (fun t : ℝ => 1 / t) volume x y := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div continuousOn_id (fun t ht => ?_)
    rw [Set.uIcc_of_le hxy] at ht
    exact (hx0.trans_le ht.1).ne'
  have hlog : ∫ t in x..y, 1 / t = Real.log (y / x) := integral_one_div_of_pos hx0 (by linarith)
  have hquad : ∀ c : ℝ, 0 ≤ Real.log (y / x) * (c * c) +
      (-2 * ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) * c +
      ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t := by
    intro c
    have h0 : 0 ≤ ∫ t in x..y, (c - ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) ^ 2 / t :=
      intervalIntegral.integral_nonneg hxy
        (fun t ht => div_nonneg (sq_nonneg _) (hx0.trans_le ht.1).le)
    have heq : ∫ t in x..y, (c - ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) ^ 2 / t =
        (c * c) * (∫ t in x..y, 1 / t) -
          (2 * c) * (∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) +
          ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (hI0.const_mul _) (hI1.const_mul _),
        ← intervalIntegral.integral_add ((hI0.const_mul _).sub (hI1.const_mul _)) (hI 2)]
      congr 1
      funext t
      ring
    rw [heq, hlog] at h0
    linarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [hd]

end GlobalTheory.Lin
