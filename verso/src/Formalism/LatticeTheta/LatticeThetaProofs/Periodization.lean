import Formalism.LatticeTheta.LatticeSummableDecay

open MeasureTheory Filter Asymptotics Complex Metric
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

namespace PoissonPeriodization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/- English proof (translation)
Take `⟨c, hc⟩` from `hO.bound`. Use `first`. Consider the case `rw [← cobounded_eq_cocompact] at hc`. Consider the case `rw [← Metric.cobounded_eq_cocompact] at hc`. Rewrite `hc` using `[← comap_norm_atTop, Filter.eventually_comap, Filter.eventually_atTop]`.

Take `⟨r, hr⟩` from `hc`. Use `set r' := max r 1 with hr'`. Take `⟨M, hM⟩` from `(isCompact_closedBall (0 : V) r').exists_bound_of_continuousOn hf.continuousOn`. Use `⟨max (M * (1 + r') ^ b) (|c| * 2 ^ b), by positivity, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : ‖v‖ ≤ r'`.

Establish `h1` using `hM v (by simpa using hv)`. Establish `hpos : 0 < 1 + ‖v‖` using `by positivity`. Establish `hr1 : 0 < 1 + r'`. Establish `: 1 ≤ r'` using `le_max_right _ _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hone : 1 ≤ (1 + r') ^ b * (1 + ‖v‖) ^ (-b)`. Rewrite using `[Real.rpow_neg hpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hpos b)]`. Conclude with `Real.rpow_le_rpow hpos.le (by linarith) hb`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_max_left _ _`.

Use `push_neg at hv`. Establish `hv1 : 1 ≤ ‖v‖` using `le_trans (le_max_right _ _) hv.le`. Establish `hb'` using `hr ‖v‖ (le_trans (le_max_left _ _) hv.le) v rfl`. Establish `hvpos : 0 < ‖v‖` using `by linarith`. Rewrite `hb'` using `[Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]`.

Establish `hk : ‖v‖ ^ (-b) ≤ 2 ^ b * (1 + ‖v‖) ^ (-b)`. Rewrite using `[Real.rpow_neg hvpos.le, Real.rpow_neg (by positivity), le_mul_inv_iff₀ (Real.rpow_pos_of_pos (by positivity) b), inv_mul_le_iff₀ (Real.rpow_pos_of_pos hvpos b), ← Real.mul_rpow hvpos.le (by norm_num : (0 : ℝ) ≤ 2)]`. Conclude with `Real.rpow_le_rpow (by positivity) (by linarith) hb`. Establish `hnn : 0 ≤ ‖v‖ ^ (-b)` using `Real.rpow_nonneg (norm_nonneg _) _`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `le_max_right _ _`.
-/
lemma exists_global_bound {f : V → ℂ} (hf : Continuous f) {b : ℝ} (hb : 0 ≤ b)
    (hO : f =O[cocompact V] (fun v => ‖v‖ ^ (-b))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖f v‖ ≤ C * (1 + ‖v‖) ^ (-b) := by
  obtain ⟨c, hc⟩ := hO.bound
  first
    | rw [← cobounded_eq_cocompact] at hc
    | rw [← Metric.cobounded_eq_cocompact] at hc
  rw [← comap_norm_atTop, Filter.eventually_comap, Filter.eventually_atTop] at hc
  obtain ⟨r, hr⟩ := hc
  set r' := max r 1 with hr'
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V) r').exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max (M * (1 + r') ^ b) (|c| * 2 ^ b), by positivity, fun v => ?_⟩
  by_cases hv : ‖v‖ ≤ r'
  · have h1 := hM v (by simpa using hv)
    have hpos : 0 < 1 + ‖v‖ := by positivity
    have hr1 : 0 < 1 + r' := by
      have : 1 ≤ r' := le_max_right _ _
      linarith
    have hone : 1 ≤ (1 + r') ^ b * (1 + ‖v‖) ^ (-b) := by
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hpos b)]
      exact Real.rpow_le_rpow hpos.le (by linarith) hb
    calc ‖f v‖ ≤ M := h1
      _ ≤ M * ((1 + r') ^ b * (1 + ‖v‖) ^ (-b)) :=
          le_mul_of_one_le_right (le_trans (norm_nonneg _) h1) hone
      _ = M * (1 + r') ^ b * (1 + ‖v‖) ^ (-b) := by ring
      _ ≤ max (M * (1 + r') ^ b) (|c| * 2 ^ b) * (1 + ‖v‖) ^ (-b) := by
          gcongr
          exact le_max_left _ _
  · push_neg at hv
    have hv1 : 1 ≤ ‖v‖ := le_trans (le_max_right _ _) hv.le
    have hb' := hr ‖v‖ (le_trans (le_max_left _ _) hv.le) v rfl
    have hvpos : 0 < ‖v‖ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hb'
    have hk : ‖v‖ ^ (-b) ≤ 2 ^ b * (1 + ‖v‖) ^ (-b) := by
      rw [Real.rpow_neg hvpos.le, Real.rpow_neg (by positivity),
        le_mul_inv_iff₀ (Real.rpow_pos_of_pos (by positivity) b),
        inv_mul_le_iff₀ (Real.rpow_pos_of_pos hvpos b),
        ← Real.mul_rpow hvpos.le (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hb
    have hnn : 0 ≤ ‖v‖ ^ (-b) := Real.rpow_nonneg (norm_nonneg _) _
    calc ‖f v‖ ≤ c * ‖v‖ ^ (-b) := hb'
      _ ≤ |c| * ‖v‖ ^ (-b) := mul_le_mul_of_nonneg_right (le_abs_self c) hnn
      _ ≤ |c| * (2 ^ b * (1 + ‖v‖) ^ (-b)) := mul_le_mul_of_nonneg_left hk (abs_nonneg c)
      _ = |c| * 2 ^ b * (1 + ‖v‖) ^ (-b) := by ring
      _ ≤ max (M * (1 + r') ^ b) (|c| * 2 ^ b) * (1 + ‖v‖) ^ (-b) := by
          gcongr
          exact le_max_right _ _

/- English proof (translation)
Establish `h1 : 0 < 1 + ‖y + x‖` using `by positivity`. Establish `h2 : 0 < 1 + ‖y‖` using `by positivity`. Establish `h3 : 0 < 1 + R` using `by linarith`. Establish `key : 1 + ‖y‖ ≤ (1 + ‖y + x‖) * (1 + R)`. Establish `hyx : ‖y‖ ≤ ‖y + x‖ + ‖x‖`.

Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[norm_nonneg (y + x)]`. Establish `key' : (1 + ‖y‖) ^ b ≤ ((1 + ‖y + x‖) * (1 + R)) ^ b` using `Real.rpow_le_rpow h2.le key hb`. Rewrite `key'` using `[Real.mul_rpow h1.le h3.le]`. Establish `hA` using `Real.rpow_pos_of_pos h1 b`.

Establish `hB` using `Real.rpow_pos_of_pos h2 b`. Rewrite using `[Real.rpow_neg h1.le, Real.rpow_neg h2.le, le_mul_inv_iff₀ hB, inv_mul_le_iff₀ hA]`. Conclude with `key'`.
-/
lemma shift_bound {b : ℝ} (hb : 0 ≤ b) {R : ℝ} (hR : 0 ≤ R) (y x : V) (hx : ‖x‖ ≤ R) :
    (1 + ‖y + x‖) ^ (-b) ≤ (1 + R) ^ b * (1 + ‖y‖) ^ (-b) := by
  have h1 : 0 < 1 + ‖y + x‖ := by positivity
  have h2 : 0 < 1 + ‖y‖ := by positivity
  have h3 : 0 < 1 + R := by linarith
  have key : 1 + ‖y‖ ≤ (1 + ‖y + x‖) * (1 + R) := by
    have hyx : ‖y‖ ≤ ‖y + x‖ + ‖x‖ := by
      calc ‖y‖ = ‖(y + x) - x‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖y + x‖ + ‖x‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (y + x)]
  have key' : (1 + ‖y‖) ^ b ≤ ((1 + ‖y + x‖) * (1 + R)) ^ b := Real.rpow_le_rpow h2.le key hb
  rw [Real.mul_rpow h1.le h3.le] at key'
  have hA := Real.rpow_pos_of_pos h1 b
  have hB := Real.rpow_pos_of_pos h2 b
  rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, le_mul_inv_iff₀ hB, inv_mul_le_iff₀ hA]
  exact key'

/- English proof (translation)
Establish `hb0 : 0 < b` using `lt_of_le_of_lt (Nat.cast_nonneg _) hb`. Establish `hr : -b < -(Module.finrank ℤ Λ : ℝ)`. Rewrite using `[ZLattice.rank ℝ Λ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs` using `ZLattice.summable_norm_rpow Λ (-b) hr`.

Use `Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) (hs.add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)` and prove the remaining obligations. Distinguish the cases in `h : l = 0`. Substitute `h` using the available equality. Simplify using `only [if_pos rfl, ZeroMemClass.coe_zero, norm_zero, add_zero, Real.one_rpow, if_true, ↓reduceIte]`. Combine the linear relations using `[Real.rpow_nonneg (le_refl (0 : ℝ)) (-b)]`.

Establish `hl : 0 < ‖(l : V)‖` using `norm_pos_iff.mpr (by simpa using h)`. Rewrite using `[if_neg h, add_zero]`. Use `show (1 + ‖(l : V)‖) ^ (-b) ≤ ‖(l : V)‖ ^ (-b)`. Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_neg hl.le]`. Conclude with `inv_anti₀ (Real.rpow_pos_of_pos hl b) (Real.rpow_le_rpow hl.le (by linarith) hb0.le)`.
-/
lemma summable_one_add_norm (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {b : ℝ} (hb : (Module.finrank ℝ V : ℝ) < b) :
    Summable (fun l : Λ => (1 + ‖(l : V)‖) ^ (-b)) := by
  classical
  have hb0 : 0 < b := lt_of_le_of_lt (Nat.cast_nonneg _) hb
  have hr : -b < -(Module.finrank ℤ Λ : ℝ) := by
    rw [ZLattice.rank ℝ Λ]
    linarith
  have hs := ZLattice.summable_norm_rpow Λ (-b) hr
  refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_)
    (hs.add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)
  by_cases h : l = 0
  · subst h
    simp only [if_pos rfl, ZeroMemClass.coe_zero, norm_zero, add_zero, Real.one_rpow, if_true, ↓reduceIte]
    linarith [Real.rpow_nonneg (le_refl (0 : ℝ)) (-b)]
  · have hl : 0 < ‖(l : V)‖ := norm_pos_iff.mpr (by simpa using h)
    rw [if_neg h, add_zero]
    show (1 + ‖(l : V)‖) ^ (-b) ≤ ‖(l : V)‖ ^ (-b)
    rw [Real.rpow_neg (by positivity), Real.rpow_neg hl.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hl b) (Real.rpow_le_rpow hl.le (by linarith) hb0.le)

end PoissonPeriodization

open PoissonPeriodization in
/- English proof (translation)
Unfold `Periodization`. Introduce `Λ _ _ f hf b hb hO`. Establish `hb0 : 0 ≤ b` using `le_trans (Nat.cast_nonneg _) hb.le`. Take `⟨C, hC0, hC⟩` from `exists_global_bound hf hb0 hO`. Establish `hS` using `summable_one_add_norm Λ hb`.

Establish `hbound : ∀ (R : ℝ), 0 ≤ R → ∀ (l : Λ) (x : V), ‖x‖ ≤ R → ‖f (↑l + x)‖ ≤ C * (1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b)`. Introduce `R hR l x hx`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `((integrable_one_add_norm hb).const_mul C).mono' hf.aestronglyMeasurable ?_` and prove the remaining obligations.

Conclude with `ae_of_all _ (fun v => hC v)`. Introduce `x first`. Consider the case `exact Summable.of_norm_bounded (hS.mul_left (C * (1 + ‖x‖) ^ b)) (fun l => hbound ‖x‖ (norm_nonneg _) l x le_rfl)`. Consider the case `exact Summable.of_norm_bounded _ (hS.mul_left (C * (1 + ‖x‖) ^ b)) (fun l => hbound ‖x‖ (norm_nonneg _) l x le_rfl)`. Use `continuous_iff_continuousAt.mpr (fun x₀ => ?_)` and prove the remaining obligations.

Establish `hcont : ContinuousOn (fun x => ∑' l : Λ, f (↑l + x)) (Metric.ball (0 : V) (‖x₀‖ + 1))`. Use `continuousOn_tsum (fun l => (hf.comp (continuous_const.add continuous_id)).continuousOn) (hS.mul_left (C * (1 + (‖x₀‖ + 1)) ^ b)) ?_` and prove the remaining obligations. Introduce `l x hx`. Conclude with `hbound (‖x₀‖ + 1) (by positivity) l x (by simpa using (Metric.mem_ball.mp hx).le)`. Conclude with `hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))`.

Introduce `l₀ x`. Establish `h` using `(Equiv.addRight l₀).tsum_eq (fun l : Λ => f (↑l + x))`. Simplify using `only [Equiv.coe_addRight, Submodule.coe_add, add_assoc] at h`. Conclude with `h`.
-/
theorem poisson_periodization (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : Periodization V := by
  unfold Periodization
  intro Λ _ _ f hf b hb hO
  have hb0 : 0 ≤ b := le_trans (Nat.cast_nonneg _) hb.le
  obtain ⟨C, hC0, hC⟩ := exists_global_bound hf hb0 hO
  have hS := summable_one_add_norm Λ hb
  have hbound : ∀ (R : ℝ), 0 ≤ R → ∀ (l : Λ) (x : V), ‖x‖ ≤ R →
      ‖f (↑l + x)‖ ≤ C * (1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b) := by
    intro R hR l x hx
    calc ‖f (↑l + x)‖ ≤ C * (1 + ‖(l : V) + x‖) ^ (-b) := hC _
      _ ≤ C * ((1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b)) :=
          mul_le_mul_of_nonneg_left (shift_bound hb0 hR (l : V) x hx) hC0
      _ = C * (1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((integrable_one_add_norm hb).const_mul C).mono' hf.aestronglyMeasurable ?_
    exact ae_of_all _ (fun v => hC v)
  · intro x
    first
      | exact Summable.of_norm_bounded (hS.mul_left (C * (1 + ‖x‖) ^ b))
          (fun l => hbound ‖x‖ (norm_nonneg _) l x le_rfl)
      | exact Summable.of_norm_bounded _ (hS.mul_left (C * (1 + ‖x‖) ^ b))
          (fun l => hbound ‖x‖ (norm_nonneg _) l x le_rfl)
  · refine continuous_iff_continuousAt.mpr (fun x₀ => ?_)
    have hcont : ContinuousOn (fun x => ∑' l : Λ, f (↑l + x)) (Metric.ball (0 : V) (‖x₀‖ + 1)) := by
      refine continuousOn_tsum (fun l => (hf.comp (continuous_const.add continuous_id)).continuousOn)
        (hS.mul_left (C * (1 + (‖x₀‖ + 1)) ^ b)) ?_
      intro l x hx
      exact hbound (‖x₀‖ + 1) (by positivity) l x (by simpa using (Metric.mem_ball.mp hx).le)
    exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))
  · intro l₀ x
    have h := (Equiv.addRight l₀).tsum_eq (fun l : Λ => f (↑l + x))
    simp only [Equiv.coe_addRight, Submodule.coe_add, add_assoc] at h
    exact h

end Formalism.H
