import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RiemannZetaOneEqOneSubOfRePos

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

open ComplexPowerDifferenceIntegral in
/- English proof (translation)
Use `set σ := s.re with hσ`. Establish `hkey : ∀ x : ℝ, 1 ≤ x → σ * (x + 1) ^ (-σ - 1) ≤ x ^ (-σ) - (x + 1) ^ (-σ)`. Introduce `x hx`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hy0 : 0 < x + 1` using `by linarith`.

Establish `hA : 0 < (x + 1) ^ σ` using `Real.rpow_pos_of_pos hy0 σ`. Establish `hB : 0 < x ^ σ` using `Real.rpow_pos_of_pos hx0 σ`. Establish `hq : 0 < (x + 1) / x` using `div_pos hy0 hx0`. Establish `hr : ((x + 1) / x) ^ σ = (x + 1) ^ σ / x ^ σ` using `Real.div_rpow hy0.le hx0.le σ`. Establish `hlog : 1 / (x + 1) ≤ Real.log ((x + 1) / x)`.

Use `Real.one_sub_inv_le_log_of_pos hq` as an intermediate fact. Establish `e : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1)` using `by field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hexp : 1 + σ / (x + 1) ≤ (x + 1) ^ σ / x ^ σ`. Rewrite using `[← hr, Real.rpow_def_of_pos hq]`.

Establish `h1` using `Real.add_one_le_exp (Real.log ((x + 1) / x) * σ)`. Establish `h2 : σ / (x + 1) ≤ Real.log ((x + 1) / x) * σ`. Rewrite using `[div_eq_mul_one_div, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right hlog hs.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Real.rpow_sub_one hy0.ne', Real.rpow_neg hy0.le, Real.rpow_neg hx0.le]`. Establish `e1 : σ * ((x + 1) ^ σ)⁻¹ / (x + 1) = σ / (x + 1) * ((x + 1) ^ σ)⁻¹` using `by ring`. Establish `e2 : (x ^ σ)⁻¹ - ((x + 1) ^ σ)⁻¹ = ((x + 1) ^ σ / x ^ σ - 1) * ((x + 1) ^ σ)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_div_assoc', e1, e2]`.

Conclude with `mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hA.le)`. Establish `hS : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), ((i : ℝ) + 1) ^ (-σ - 1) ≤ 1 + (1 - ((N : ℝ) + 1) ^ (-σ)) / σ`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => simp`.

Consider the case `succ N ih`. Rewrite using `[Finset.sum_range_succ]`. Establish `hk` using `hkey ((N : ℝ) + 1) (by linarith [N.cast_nonneg (α := ℝ)])`. Establish `hk' : ((N : ℝ) + 1 + 1) ^ (-σ - 1) ≤ (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ`. Rewrite using `[le_div_iff₀ hs]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`. Establish `e : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ + (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ = (1 - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) ≤ 1 + 1 / σ`. Introduce `n`. Break down `n with _ | N` into its components or cases. Simplify using `only [Finset.range_zero, Finset.sum_empty]`.

Check the signs of the components of the expression. Use `(hS N).trans ?_` and prove the remaining obligations. Establish `h0 : 0 ≤ ((N : ℝ) + 1) ^ (-σ)` using `Real.rpow_nonneg (by positivity) _`. Establish `: (1 - ((N : ℝ) + 1) ^ (-σ)) / σ ≤ 1 / σ` using `div_le_div_of_nonneg_right (by linarith) hs.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hC : 0 ≤ ‖s - 1‖ * ‖s‖` using `by positivity`. Use `show ‖∑' n, dz s n‖ ≤ _`. Combine the equalities or inequalities in the displayed calculation. Use `Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) fun n => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]`. Use `_ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := mul_le_mul_of_nonneg_left (hT n) hC`.
-/
lemma norm_Dz_le {s : ℂ} (hs : 0 < s.re) :
    ‖Dz s‖ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
  set σ := s.re with hσ

  have hkey : ∀ x : ℝ, 1 ≤ x → σ * (x + 1) ^ (-σ - 1) ≤ x ^ (-σ) - (x + 1) ^ (-σ) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < x + 1 := by linarith
    have hA : 0 < (x + 1) ^ σ := Real.rpow_pos_of_pos hy0 σ
    have hB : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    have hq : 0 < (x + 1) / x := div_pos hy0 hx0
    have hr : ((x + 1) / x) ^ σ = (x + 1) ^ σ / x ^ σ := Real.div_rpow hy0.le hx0.le σ
    have hlog : 1 / (x + 1) ≤ Real.log ((x + 1) / x) := by
      have := Real.one_sub_inv_le_log_of_pos hq
      have e : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
      linarith
    have hexp : 1 + σ / (x + 1) ≤ (x + 1) ^ σ / x ^ σ := by
      rw [← hr, Real.rpow_def_of_pos hq]
      have h1 := Real.add_one_le_exp (Real.log ((x + 1) / x) * σ)
      have h2 : σ / (x + 1) ≤ Real.log ((x + 1) / x) * σ := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_right hlog hs.le
      linarith
    rw [Real.rpow_sub_one hy0.ne', Real.rpow_neg hy0.le, Real.rpow_neg hx0.le]
    have e1 : σ * ((x + 1) ^ σ)⁻¹ / (x + 1) = σ / (x + 1) * ((x + 1) ^ σ)⁻¹ := by ring
    have e2 : (x ^ σ)⁻¹ - ((x + 1) ^ σ)⁻¹ = ((x + 1) ^ σ / x ^ σ - 1) * ((x + 1) ^ σ)⁻¹ := by
      field_simp
    rw [mul_div_assoc', e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hA.le)
  have hS : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), ((i : ℝ) + 1) ^ (-σ - 1)
      ≤ 1 + (1 - ((N : ℝ) + 1) ^ (-σ)) / σ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hk := hkey ((N : ℝ) + 1) (by linarith [N.cast_nonneg (α := ℝ)])
      have hk' : ((N : ℝ) + 1 + 1) ^ (-σ - 1) ≤ (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ := by
        rw [le_div_iff₀ hs]
        linarith
      push_cast
      have e : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ + (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ
          = (1 - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ := by
        field_simp
        ring
      linarith
  have hT : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) ≤ 1 + 1 / σ := by
    intro n
    rcases n with _ | N
    · simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    · refine (hS N).trans ?_
      have h0 : 0 ≤ ((N : ℝ) + 1) ^ (-σ) := Real.rpow_nonneg (by positivity) _
      have : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ ≤ 1 / σ := div_le_div_of_nonneg_right (by linarith) hs.le
      linarith
  have hC : 0 ≤ ‖s - 1‖ * ‖s‖ := by positivity
  show ‖∑' n, dz s n‖ ≤ _
  calc ‖∑' n, dz s n‖ ≤ ∑' n, ‖dz s n‖ := norm_tsum_le_tsum_norm (summable_norm_dz hs)
    _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := by
      refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) fun n => ?_
      calc ∑ i ∈ Finset.range n, ‖dz s i‖
          ≤ ∑ i ∈ Finset.range n, ‖s - 1‖ * ‖s‖ * ((i : ℝ) + 1) ^ (-σ - 1) :=
            Finset.sum_le_sum fun i _ => norm_dz_le hs i
        _ = ‖s - 1‖ * ‖s‖ * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) := by
            rw [Finset.mul_sum]
        _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := mul_le_mul_of_nonneg_left (hT n) hC

/- English proof (translation)
Introduce `s hs hs1`. Establish `h1 : riemannZeta₁ s = (s - 1) * riemannZeta s`. Unfold `riemannZeta₁ riemannZeta₀`. Rewrite using `[if_neg hs1, mul_sub, mul_inv_cancel₀ (sub_ne_zero.2 hs1)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hD` using `norm_Dz_le hs`. Establish `hne : s - 1 ≠ 0` using `sub_ne_zero.2 hs1`. Establish `hpos : 0 < ‖s - 1‖` using `norm_pos_iff.2 hne`. Establish `hz : riemannZeta s = (s - ComplexPowerDifferenceIntegral.Dz s) / (s - 1)`. Rewrite using `[← ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hs, h1]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hz, norm_div, div_le_iff₀ hpos]`. Establish `hs' : ‖s‖ ≤ ‖s - 1‖ + 1` using `by simpa using norm_add_le (s - 1) 1`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.
-/
theorem growthBound : ZetaGrowth := by
  intro s hs hs1
  have h1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    unfold riemannZeta₁ riemannZeta₀
    rw [if_neg hs1, mul_sub, mul_inv_cancel₀ (sub_ne_zero.2 hs1)]
    ring
  have hD := norm_Dz_le hs
  have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hpos : 0 < ‖s - 1‖ := norm_pos_iff.2 hne
  have hz : riemannZeta s = (s - ComplexPowerDifferenceIntegral.Dz s) / (s - 1) := by
    rw [← ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hs, h1]
    field_simp
  rw [hz, norm_div, div_le_iff₀ hpos]
  have hs' : ‖s‖ ≤ ‖s - 1‖ + 1 := by simpa using norm_add_le (s - 1) 1
  calc ‖s - ComplexPowerDifferenceIntegral.Dz s‖ ≤ ‖s‖ + ‖ComplexPowerDifferenceIntegral.Dz s‖ := norm_sub_le _ _
    _ ≤ (‖s - 1‖ + 1) + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := add_le_add hs' hD
    _ = (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) * ‖s - 1‖ := by
        field_simp

end Formalism.ZF
