import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicValueDerivativeL2BallStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.JetSmall

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[zero_nsmul, Nat.cast_zero, zero_mul]`. Use `A.ph_add 0 0 i y hy` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ k ih`. Rewrite using `[succ_nsmul, A.ph_add _ _ i y hy, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ph_nsmul {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (H : La) (i : ι) (y : Y) (hy : y ∈ (A.chart i).source) (k : ℕ) :
    A.ph (k • H) i y = k * A.ph H i y := by
  induction k with
  | zero =>
    rw [zero_nsmul, Nat.cast_zero, zero_mul]
    have := A.ph_add 0 0 i y hy
    rw [add_zero] at this
    linarith
  | succ k ih =>
    rw [succ_nsmul, A.ph_add _ _ i y hy, ih]
    push_cast; ring

/- English proof (translation)
Introduce `n Y _ _ _ _ _ ι La _ A H G i p r0 c Cq K q hr0 hc hsub hq hH ε hε`. Use `set r : ℝ := min r0 (Real.sqrt (c / (2 * (|Cq| + 1)))) with hr`. Establish `hCq1 : 0 < |Cq| + 1` using `by positivity`. Establish `hrpos : 0 < r` using `lt_min hr0 (Real.sqrt_pos.2 (by positivity))`. Establish `hrr0 : r ≤ r0` using `min_le_left _ _`.

Establish `hr2 : r ^ 2 ≤ c / (2 * (|Cq| + 1))`. Establish `h1 : r ≤ Real.sqrt (c / (2 * (|Cq| + 1)))` using `min_le_right _ _`. Establish `h2` using `pow_le_pow_left₀ hrpos.le h1 2`. Rewrite `h2` using `[Real.sq_sqrt (by positivity)]`. Then use the resulting hypothesis. Establish `hsubr : closedBall p r ⊆ (A.chart i).target` using `(closedBall_subset_closedBall hrr0).trans hsub`.

Establish `hball : ball p r ⊆ (A.chart i).target` using `ball_subset_closedBall.trans hsubr`. Establish `hquad : ∀ v ∈ closedBall p r, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ c / 2`. Introduce `v hv`. Establish `h` using `hH v (closedBall_subset_closedBall hrr0 hv)`. Establish `hd : ‖v - p‖ ≤ r` using `by rw [← dist_eq_norm]; exact hv`.

Establish `hd2 : ‖v - p‖ ^ 2 ≤ r ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hd 2`. Establish `h3 : Cq * ‖v - p‖ ^ 2 ≤ |Cq| * ‖v - p‖ ^ 2` using `mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)`. Establish `h4 : |Cq| * ‖v - p‖ ^ 2 ≤ |Cq| * (c / (2 * (|Cq| + 1)))` using `mul_le_mul_of_nonneg_left (hd2.trans hr2) (abs_nonneg _)`. Establish `h5 : |Cq| * (c / (2 * (|Cq| + 1))) ≤ c / 2`. Rewrite using `[mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]`.

Use polynomial arithmetic with `[abs_nonneg Cq]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨M, hM⟩` from `hyq_bdd (f := fun v => Real.exp (A.ph G i ((A.chart i).symm v))) (c := p) (r := r) ((A.smooth_ph G i).continuousOn.rexp.mono hsubr)`. Establish `hM0 : 0 ≤ M` using `(Real.exp_pos _).le.trans (hM p (mem_closedBall_self hrpos.le))`. Take `⟨C, hC0, hC⟩` from `GlobalTheory.T.holomorphic_value_derivative_l2_ball n r hrpos`.

Establish `htend : Tendsto (fun k : ℕ => C * M * |K| * Real.exp (-(c / 2) * k)) atTop (𝓝 0)`. Establish `h1 : Tendsto (fun k : ℕ => -(c / 2) * (k : ℝ)) atTop atBot` using `(tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (by linarith)`. Establish `h2` using `(Real.tendsto_exp_atBot.comp h1).const_mul (C * M * |K|)`. Simplify using `using h2`. Take `⟨k0, hk0⟩` from `eventually_atTop.1 ((tendsto_order.1 htend).2 (ε ^ 2) (by positivity))`.

Use `⟨k0, fun k hk D hD hDd hn0 => ?_⟩` and prove the remaining obligations. Use `set u : V n → ℂ := fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v)) with hu`. Establish `hud : DifferentiableOn ℂ u (ball p r)` using `(hDd.mono (ball_subset_ball hrr0)).mul ((Complex.differentiable_exp.comp ((hq.const_mul (k : ℂ)).neg)).differentiableOn)`. Establish `hest` using `hC p u hud`. Use `set la : La := G + k • H`.

Use `set f : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y) with hf`. Establish `hfm : Measurable f` using `ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq _ D hD.2 (fun j => (hD.1 j).continuousOn)).measurable`. Establish `hpt : ∀ v ∈ ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤ ENNReal.ofReal (M * Real.exp (k * (c / 2))) * (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))`. Introduce `v hv`. Use `set y := (A.chart i).symm v`.

Establish `hy : y ∈ (A.chart i).source` using `(A.chart i).map_target (hball hv)`. Establish `hns` using `hyq_nsq_chart A (A.kap + la) D i y hy (hD.2 i (A.pick y) y hy (A.mem_pick y))`. Establish `hph : A.ph (A.kap + la) i y = A.ph A.kap i y + (A.ph G i y + k * A.ph H i y)`. Rewrite using `[A.ph_add _ _ i y hy, A.ph_add _ _ i y hy, ph_nsmul A H i y hy]`. Simplify using `only [hf]`.

Rewrite using `[hns, hph, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hnu : ‖u v‖ ^ 2 = ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re))`. Simplify using `only [hu, norm_mul, Complex.norm_exp, mul_pow]`. Use `congr 1`.

Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Simplify using `[Complex.neg_re, Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hnu]`.

Establish `hq2` using `hquad v (ball_subset_closedBall hv)`. Establish `hMv` using `hM v (ball_subset_closedBall hv)`. Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `key : Real.exp (-(2 * k * (q v).re)) ≤ M * Real.exp (k * (c / 2)) * (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) * Real.exp (A.ph A.kap i y))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.exp_add, ← Real.exp_add, ← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hq2 hk0]`. Use `_ ≤ _ := by gcongr`. Combine the equalities or inequalities in the displayed calculation.

Establish `hint : ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤ ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D`. Combine the equalities or inequalities in the displayed calculation. Conclude with `A.aap_lintegral_chart_le i f hfm _ hball`. Establish `hall : ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤ ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k))`. Combine the equalities or inequalities in the displayed calculation.

Use `hest.trans ?_` and prove the remaining obligations. Use `gcongr`. Use `hint.trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `hn0.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le))`.

Use `_ = ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by`. Rewrite using `[← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]`. Use `congr 1`. Establish `: Real.exp (k * (c / 2)) * Real.exp (-c * k) = Real.exp (-(c / 2) * k)`. Rewrite using `[← Real.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Establish `hsq : ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2`. Establish `hb` using `(hk0 k hk).le`.

Break down `(ENNReal.ofReal_le_ofReal_iff'.1 hall) with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[sq_nonneg ε]`. Establish `h1 : ‖u p‖ ^ 2 ≤ ε ^ 2` using `by nlinarith [sq_nonneg ‖fderiv ℂ u p‖]`. Establish `h2 : ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2` using `by nlinarith [sq_nonneg ‖u p‖]`.

Conclude with `⟨by nlinarith [norm_nonneg (u p)], by nlinarith [norm_nonneg (fderiv ℂ u p)]⟩`.
-/
theorem main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H G : La) (i : ι) (p : V n) (r0 c Cq K : ℝ) (q : V n → ℂ), 0 < r0 → 0 < c → closedBall p r0 ⊆ (A.chart i).target → Differentiable ℂ q → (∀ v ∈ closedBall p r0, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ Cq * ‖v - p‖ ^ 2) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ D : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) D → DifferentiableOn ℂ (D i ∘ (A.chart i).symm) (ball p r0) → n0 A (G + k • H) D ≤ ENNReal.ofReal (K * Real.exp (-c * k)) → ‖D i ((A.chart i).symm p) * Complex.exp (-(k * q p))‖ ≤ ε ∧ ‖fderiv ℂ (fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v))) p‖ ≤ ε := by
  intro n Y _ _ _ _ _ ι La _ A H G i p r0 c Cq K q hr0 hc hsub hq hH ε hε

  set r : ℝ := min r0 (Real.sqrt (c / (2 * (|Cq| + 1)))) with hr
  have hCq1 : 0 < |Cq| + 1 := by positivity
  have hrpos : 0 < r := lt_min hr0 (Real.sqrt_pos.2 (by positivity))
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hr2 : r ^ 2 ≤ c / (2 * (|Cq| + 1)) := by
    have h1 : r ≤ Real.sqrt (c / (2 * (|Cq| + 1))) := min_le_right _ _
    have h2 := pow_le_pow_left₀ hrpos.le h1 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hsubr : closedBall p r ⊆ (A.chart i).target :=
    (closedBall_subset_closedBall hrr0).trans hsub
  have hball : ball p r ⊆ (A.chart i).target := ball_subset_closedBall.trans hsubr
  have hquad : ∀ v ∈ closedBall p r, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ c / 2 := by
    intro v hv
    have h := hH v (closedBall_subset_closedBall hrr0 hv)
    have hd : ‖v - p‖ ≤ r := by rw [← dist_eq_norm]; exact hv
    have hd2 : ‖v - p‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    have h3 : Cq * ‖v - p‖ ^ 2 ≤ |Cq| * ‖v - p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h4 : |Cq| * ‖v - p‖ ^ 2 ≤ |Cq| * (c / (2 * (|Cq| + 1))) :=
      mul_le_mul_of_nonneg_left (hd2.trans hr2) (abs_nonneg _)
    have h5 : |Cq| * (c / (2 * (|Cq| + 1))) ≤ c / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg Cq]
    linarith

  obtain ⟨M, hM⟩ := hyq_bdd (f := fun v => Real.exp (A.ph G i ((A.chart i).symm v))) (c := p) (r := r)
    ((A.smooth_ph G i).continuousOn.rexp.mono hsubr)
  have hM0 : 0 ≤ M := (Real.exp_pos _).le.trans (hM p (mem_closedBall_self hrpos.le))

  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.holomorphic_value_derivative_l2_ball n r hrpos

  have htend : Tendsto (fun k : ℕ => C * M * |K| * Real.exp (-(c / 2) * k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => -(c / 2) * (k : ℝ)) atTop atBot :=
      (tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (by linarith)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (C * M * |K|)
    simpa using h2
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 ((tendsto_order.1 htend).2 (ε ^ 2) (by positivity))
  refine ⟨k0, fun k hk D hD hDd hn0 => ?_⟩
  set u : V n → ℂ := fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v)) with hu
  have hud : DifferentiableOn ℂ u (ball p r) :=
    (hDd.mono (ball_subset_ball hrr0)).mul
      ((Complex.differentiable_exp.comp ((hq.const_mul (k : ℂ)).neg)).differentiableOn)
  have hest := hC p u hud

  set la : La := G + k • H
  set f : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y) with hf
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq _ D hD.2
      (fun j => (hD.1 j).continuousOn)).measurable

  have hpt : ∀ v ∈ ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤
      ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
        (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) := by
    intro v hv
    set y := (A.chart i).symm v
    have hy : y ∈ (A.chart i).source := (A.chart i).map_target (hball hv)
    have hns := hyq_nsq_chart A (A.kap + la) D i y hy (hD.2 i (A.pick y) y hy (A.mem_pick y))
    have hph : A.ph (A.kap + la) i y = A.ph A.kap i y + (A.ph G i y + k * A.ph H i y) := by
      rw [A.ph_add _ _ i y hy, A.ph_add _ _ i y hy, ph_nsmul A H i y hy]
    simp only [hf]
    rw [hns, hph, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hnu : ‖u v‖ ^ 2 = ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re)) := by
      simp only [hu, norm_mul, Complex.norm_exp, mul_pow]
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      simp [Complex.neg_re, Complex.mul_re]
      ring
    rw [hnu]
    have hq2 := hquad v (ball_subset_closedBall hv)
    have hMv := hM v (ball_subset_closedBall hv)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have key : Real.exp (-(2 * k * (q v).re)) ≤
        M * Real.exp (k * (c / 2)) * (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) *
          Real.exp (A.ph A.kap i y)) := by
      calc Real.exp (-(2 * k * (q v).re))
          ≤ Real.exp (A.ph G i y) * Real.exp (k * (c / 2)) *
              (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) *
                Real.exp (A.ph A.kap i y)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            apply Real.exp_le_exp.2
            nlinarith [mul_le_mul_of_nonneg_left hq2 hk0]
        _ ≤ _ := by gcongr
    calc ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re))
        ≤ ‖D i y‖ ^ 2 * (M * Real.exp (k * (c / 2)) *
          (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) * Real.exp (A.ph A.kap i y))) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring
  have hint : ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤
      ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D := by
    calc ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2)
        ≤ ∫⁻ v in ball p r, ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
            (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (M * Real.exp (k * (c / 2))) * ∫⁻ v in ball p r,
            f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D := by
          gcongr
          exact A.aap_lintegral_chart_le i f hfm _ hball

  have hall : ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
      ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by
    calc ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
            ENNReal.ofReal (|K| * Real.exp (-c * k))) := by
          refine hest.trans ?_
          gcongr
          refine hint.trans ?_
          gcongr
          exact hn0.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le))
      _ = ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
          congr 1
          have : Real.exp (k * (c / 2)) * Real.exp (-c * k) = Real.exp (-(c / 2) * k) := by
            rw [← Real.exp_add]; congr 1; ring
          calc C * (M * Real.exp (k * (c / 2)) * (|K| * Real.exp (-c * k)))
              = C * M * |K| * (Real.exp (k * (c / 2)) * Real.exp (-c * k)) := by ring
            _ = _ := by rw [this]
  have hsq : ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2 := by
    have hb := (hk0 k hk).le
    rcases (ENNReal.ofReal_le_ofReal_iff'.1 hall) with h | h
    · linarith
    · nlinarith [sq_nonneg ε]
  have h1 : ‖u p‖ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ‖fderiv ℂ u p‖]
  have h2 : ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ‖u p‖]
  exact ⟨by nlinarith [norm_nonneg (u p)], by nlinarith [norm_nonneg (fderiv ℂ u p)]⟩

end GlobalTheory.JetSmall
