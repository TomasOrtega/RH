import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.GL3MeanSquares.HookFormulaTorsion.SmoothedRemainderRealHasDerivBound

open Finset Filter Topology ArithmeticFunction MeasureTheory

namespace Formalism.HermitianLattices.GL2a2

open Formalism.HermitianLattices.GL2PrimeSums

/- English proof (translation)
Proceed by induction on `Zs using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons ρ Z ih`. Simplify using `only [Multiset.map_cons, Multiset.sum_cons]`. Establish `ih'` using `ih (fun r hr => hre r (Multiset.mem_cons_of_mem hr))`.

Establish `h1 : ‖(u : ℂ) ^ ρ / ρ‖ ≤ B * (1 / ‖ρ‖)`. Rewrite using `[norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0, div_eq_mul_one_div]`. Conclude with `mul_le_mul_of_nonneg_right (hre ρ (Multiset.mem_cons_self _ _)) (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma norm_sum_zeros_le (u B : ℝ) (hu0 : 0 < u) (Zs : Multiset ℂ)
    (hre : ∀ ρ ∈ Zs, u ^ ρ.re ≤ B) :
    ‖(Zs.map (fun ρ => (u : ℂ) ^ ρ / ρ)).sum‖ ≤ B * (Zs.map (fun ρ => 1 / ‖ρ‖)).sum := by
  induction Zs using Multiset.induction_on with
  | empty => simp
  | cons ρ Z ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have ih' := ih (fun r hr => hre r (Multiset.mem_cons_of_mem hr))
    have h1 : ‖(u : ℂ) ^ ρ / ρ‖ ≤ B * (1 / ‖ρ‖) := by
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (hre ρ (Multiset.mem_cons_self _ _)) (by positivity)
    calc _ ≤ ‖(u : ℂ) ^ ρ / ρ‖ + ‖(Z.map (fun ρ => (u : ℂ) ^ ρ / ρ)).sum‖ := norm_add_le _ _
      _ ≤ _ := by rw [mul_add]; exact add_le_add h1 ih'

/- English proof (translation)
Rewrite using `[Real.lt_log_iff_exp_lt (by norm_num)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/- English proof (translation)
Introduce `c C₂ hc hC₂`. Use `⟨288 * C₂ / c ^ 2, c / 6, by positivity, by positivity, ?_⟩` and prove the remaining obligations. Introduce `Q u Zs hQ hu hz hsum`. Establish `hQ0 : 0 < Q` using `by linarith`. Establish `hlQ : 1 < Real.log Q` using `lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hQ)`.

Establish `hu0 : 0 < u` using `lt_of_lt_of_le (Real.exp_pos _) hu`. Establish `hlu : Real.log Q ^ 2 ≤ Real.log u`. Rewrite using `[Real.le_log_iff_exp_le hu0]`. Conclude with `hu`. Use `set s := Real.sqrt (Real.log u) with hs`.

Establish `hlu0 : 0 ≤ Real.log u` using `le_trans (sq_nonneg _) hlu`. Establish `hss : s ^ 2 = Real.log u` using `Real.sq_sqrt hlu0`. Establish `hsQ : Real.log Q ≤ s` using `Real.le_sqrt_of_sq_le hlu`. Establish `hs1 : 1 < s` using `lt_of_lt_of_le hlQ hsQ`. Establish `hs0 : 0 < s` using `by linarith`.

Establish `hB : ∀ ρ ∈ Zs, u ^ ρ.re ≤ u * Real.exp (-(c / 3) * s)`. Introduce `ρ hρ`. Take `⟨him, hre⟩` from `hz ρ hρ`. Establish `ha0 : 0 ≤ |ρ.im|` using `abs_nonneg _`. Establish `hx : (2.7 : ℝ) < Real.exp s`.

Establish `h1 : Real.exp 1 < Real.exp s` using `Real.exp_lt_exp.mpr hs1`. Use `Real.exp_one_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : |ρ.im| + 3 ≤ Real.exp (2 * s)`. Establish `: Real.exp (2 * s) = Real.exp s * Real.exp s` using `by rw [← Real.exp_add]; ring_nf`.

Rewrite using `[this]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlog : Real.log (Q * (|ρ.im| + 3)) ≤ 3 * s`. Rewrite using `[Real.log_mul hQ0.ne' (by positivity)]`. Establish `: Real.log (|ρ.im| + 3) ≤ 2 * s`.

Rewrite using `[Real.log_le_iff_le_exp (by positivity)]; exact h3`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog0 : 0 < Real.log (Q * (|ρ.im| + 3))` using `Real.log_pos (by nlinarith)`. Establish `hdiv : c / (3 * s) ≤ c / Real.log (Q * (|ρ.im| + 3))` using `div_le_div_of_nonneg_left hc.le hlog0 hlog`. Establish `hre' : ρ.re ≤ 1 - c / (3 * s)` using `by linarith`.

Establish `hu1 : 1 ≤ u`. Rewrite using `[← Real.log_nonneg_iff hu0]`. Conclude with `hlu0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_sub hu0, Real.rpow_one, Real.rpow_def_of_pos hu0, ← hss, div_eq_mul_inv, ← Real.exp_neg]`.

Use `congr 2`. Clear the denominators using the available nonvanishing facts. Establish `h1` using `norm_sum_zeros_le u _ hu0 Zs hB`. Establish `hsum' : (Zs.map (fun ρ => 1 / ‖ρ‖)).sum ≤ C₂ * (4 * s ^ 2)`. Use `hsum.trans ?_` and prove the remaining obligations.

Rewrite using `[Real.log_mul hQ0.ne' (Real.exp_pos _).ne', Real.log_exp]`. Establish `: (Real.log Q + s) ^ 2 ≤ 4 * s ^ 2` using `by nlinarith`. Conclude with `mul_le_mul_of_nonneg_left this hC₂.le`. Establish `hE : s ^ 2 * Real.exp (-(c / 3) * s) ≤ 72 / c ^ 2 * Real.exp (-(c / 6) * s)`. Establish `e : Real.exp (-(c / 3) * s) = Real.exp (-(c / 6) * s) * Real.exp (-(c / 6) * s)`.

Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Establish `hq : (c / 6 * s) ^ 2 / 2 ≤ Real.exp (c / 6 * s)`. Use `Real.quadratic_le_exp_of_nonneg (x := c / 6 * s) (by positivity)` as an intermediate fact. Use polynomial arithmetic with `[mul_pos hc hs0]`.

Establish `hq' : s ^ 2 * Real.exp (-(c / 6) * s) ≤ 72 / c ^ 2`. Establish `e2 : Real.exp (-(c / 6) * s) = (Real.exp (c / 6 * s))⁻¹` using `by rw [← Real.exp_neg]; ring_nf`. Rewrite using `[e2, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]`. Establish `: s ^ 2 = 72 / c ^ 2 * ((c / 6 * s) ^ 2 / 2)` using `by field_simp; ring`. Rewrite using `[this]`.

Conclude with `mul_le_mul_of_nonneg_left hq (by positivity)`. Rewrite using `[e, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right hq' (Real.exp_pos _).le`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem zero_sum_bound_large : Formalism.HermitianLattices.GL2a2.ZeroSumBoundLarge := by
  intro c C₂ hc hC₂
  refine ⟨288 * C₂ / c ^ 2, c / 6, by positivity, by positivity, ?_⟩
  intro Q u Zs hQ hu hz hsum
  have hQ0 : 0 < Q := by linarith
  have hlQ : 1 < Real.log Q := lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hQ)
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
  have hlu : Real.log Q ^ 2 ≤ Real.log u := by
    rw [Real.le_log_iff_exp_le hu0]; exact hu
  set s := Real.sqrt (Real.log u) with hs
  have hlu0 : 0 ≤ Real.log u := le_trans (sq_nonneg _) hlu
  have hss : s ^ 2 = Real.log u := Real.sq_sqrt hlu0
  have hsQ : Real.log Q ≤ s := Real.le_sqrt_of_sq_le hlu
  have hs1 : 1 < s := lt_of_lt_of_le hlQ hsQ
  have hs0 : 0 < s := by linarith

  have hB : ∀ ρ ∈ Zs, u ^ ρ.re ≤ u * Real.exp (-(c / 3) * s) := by
    intro ρ hρ
    obtain ⟨him, hre⟩ := hz ρ hρ
    have ha0 : 0 ≤ |ρ.im| := abs_nonneg _
    have hx : (2.7 : ℝ) < Real.exp s := by
      have h1 : Real.exp 1 < Real.exp s := Real.exp_lt_exp.mpr hs1
      have := Real.exp_one_gt_d9
      linarith
    have h3 : |ρ.im| + 3 ≤ Real.exp (2 * s) := by
      have : Real.exp (2 * s) = Real.exp s * Real.exp s := by rw [← Real.exp_add]; ring_nf
      rw [this]; nlinarith
    have hlog : Real.log (Q * (|ρ.im| + 3)) ≤ 3 * s := by
      rw [Real.log_mul hQ0.ne' (by positivity)]
      have : Real.log (|ρ.im| + 3) ≤ 2 * s := by
        rw [Real.log_le_iff_le_exp (by positivity)]; exact h3
      linarith
    have hlog0 : 0 < Real.log (Q * (|ρ.im| + 3)) := Real.log_pos (by nlinarith)
    have hdiv : c / (3 * s) ≤ c / Real.log (Q * (|ρ.im| + 3)) :=
      div_le_div_of_nonneg_left hc.le hlog0 hlog
    have hre' : ρ.re ≤ 1 - c / (3 * s) := by linarith
    have hu1 : 1 ≤ u := by
      rw [← Real.log_nonneg_iff hu0]; exact hlu0
    calc u ^ ρ.re ≤ u ^ (1 - c / (3 * s)) := Real.rpow_le_rpow_of_exponent_le hu1 hre'
      _ = u * Real.exp (-(c / 3) * s) := by
        rw [Real.rpow_sub hu0, Real.rpow_one, Real.rpow_def_of_pos hu0, ← hss, div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        field_simp
  have h1 := norm_sum_zeros_le u _ hu0 Zs hB
  have hsum' : (Zs.map (fun ρ => 1 / ‖ρ‖)).sum ≤ C₂ * (4 * s ^ 2) := by
    refine hsum.trans ?_
    rw [Real.log_mul hQ0.ne' (Real.exp_pos _).ne', Real.log_exp]
    have : (Real.log Q + s) ^ 2 ≤ 4 * s ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hC₂.le
  have hE : s ^ 2 * Real.exp (-(c / 3) * s) ≤ 72 / c ^ 2 * Real.exp (-(c / 6) * s) := by
    have e : Real.exp (-(c / 3) * s) = Real.exp (-(c / 6) * s) * Real.exp (-(c / 6) * s) := by
      rw [← Real.exp_add]; ring_nf
    have hq : (c / 6 * s) ^ 2 / 2 ≤ Real.exp (c / 6 * s) := by
      have := Real.quadratic_le_exp_of_nonneg (x := c / 6 * s) (by positivity)
      nlinarith [mul_pos hc hs0]
    have hq' : s ^ 2 * Real.exp (-(c / 6) * s) ≤ 72 / c ^ 2 := by
      have e2 : Real.exp (-(c / 6) * s) = (Real.exp (c / 6 * s))⁻¹ := by rw [← Real.exp_neg]; ring_nf
      rw [e2, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      have : s ^ 2 = 72 / c ^ 2 * ((c / 6 * s) ^ 2 / 2) := by field_simp; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hq (by positivity)
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hq' (Real.exp_pos _).le
  calc ‖(Zs.map (fun ρ => (u : ℂ) ^ ρ / ρ)).sum‖
      ≤ u * Real.exp (-(c / 3) * s) * (Zs.map (fun ρ => 1 / ‖ρ‖)).sum := h1
    _ ≤ u * Real.exp (-(c / 3) * s) * (C₂ * (4 * s ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = 4 * C₂ * u * (s ^ 2 * Real.exp (-(c / 3) * s)) := by ring
    _ ≤ 4 * C₂ * u * (72 / c ^ 2 * Real.exp (-(c / 6) * s)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = 288 * C₂ / c ^ 2 * u * Real.exp (-(c / 6) * s) := by ring

end Formalism.HermitianLattices.GL2a2
