import Mathlib

open Filter Topology Metric Set

namespace GlobalTheory

/- English proof (translation)
Establish `h1` using `hs.tsum_fiberwise deg`. Establish `e : (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) = (fun k => ∑' i : deg ⁻¹' {k}, c i * x ^ deg i)`. Use function extensionality and compare the values at `k`. Rewrite using `[← tsum_mul_right]`. Apply `tsum_congr` to reduce the goal to its premises.

Introduce and unpack `⟨i, hi⟩`. Simplify using `only [mem_preimage, mem_singleton_iff] at hi`. Simplify using `[hi]`. Rewrite using `[e]`. Conclude with `h1`.
-/
theorem gradedSeries_regroup {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (x s : ℂ)
    (hs : HasSum (fun i => c i * x ^ deg i) s) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) s := by
  have h1 := hs.tsum_fiberwise deg
  have e : (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) =
      (fun k => ∑' i : deg ⁻¹' {k}, c i * x ^ deg i) := by
    funext k
    rw [← tsum_mul_right]
    apply tsum_congr
    rintro ⟨i, hi⟩
    simp only [mem_preimage, mem_singleton_iff] at hi
    simp [hi]
  rw [e]
  exact h1

/- English proof (translation)
Use `set A : ℕ → ℂ := fun k => ∑' i : deg ⁻¹' {k}, c i with hAdef`. Use `set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ A with hpdef`. Establish `hx0 : 0 < δ / 2` using `by positivity`. Use `set x0 : NNReal := ⟨δ / 2, hx0.le⟩ with hx0def`. Establish `hrad : (x0 : ENNReal) ≤ p.radius`.

Apply `p.le_radius_of_summable_norm` to reduce the goal to its premises. Establish `hs` using `(gradedSeries_regroup deg c _ _ (h (δ / 2) hx0 (by linarith))).summable`. Establish `hs'` using `summable_norm_iff.mpr hs`. Use `hs'.congr fun n => ?_` and prove the remaining obligations. Simplify using `only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]`.

Both sides reduce to the same expression. Establish `hF` using `p.hasFPowerSeriesOnBall (lt_of_lt_of_le (ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos]; exact hx0)) hrad)`. Establish `hρ : 0 < ρ` using `lt_of_le_of_lt (norm_nonneg _) hX`. Establish `hs0 : 0 < min (δ / 2) ρ` using `lt_min hx0 hρ`. Establish `hQan : AnalyticOnNhd ℂ Q (ball 0 ρ)` using `hQ.analyticOnNhd isOpen_ball`.

Establish `hmem : ∀ z : ℂ, ‖z‖ < δ / 2 → z ∈ EMetric.ball (0 : ℂ) p.radius`. Introduce `z hz`. Express the relevant statement in the definitionally equal form `edist _ (0 : ℂ) < _`. Rewrite using `[edist_zero_right]`. Use `lt_of_lt_of_le ?_ hrad` and prove the remaining obligations.

Conclude with `ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; exact hz)`. Establish `hFan : AnalyticOnNhd ℂ p.sum (ball 0 (min (δ / 2) ρ))` using `fun z hz => hF.analyticAt_of_mem (hmem z (lt_of_lt_of_le (by simpa using hz) (min_le_left _ _)))`. Establish `ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0)` using `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall fun x hx => by simpa using (ne_of_gt hx))`. Establish `hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), p.sum z = Q z`. Use `ht.frequently (Filter.Eventually.frequently ?_)` and prove the remaining obligations.

Use `filter_upwards [Ioo_mem_nhdsGT hx0] with x hx`. Establish `h1` using `gradedSeries_regroup deg c _ _ (h x hx.1 (by linarith [hx.2]))`. Simplify using `only [p, FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]`. Conclude with `h1.tsum_eq`. Establish `heq : EqOn p.sum Q (ball 0 (min (δ / 2) ρ))` using `hFan.eqOn_of_preconnected_of_frequently_eq (hQan.mono (ball_subset_ball (min_le_right _ _))) (convex_ball _ _).isPreconnected (mem_ball_self hs0) hfreq`.

Establish `hQp : HasFPowerSeriesAt Q p 0` using `hF.hasFPowerSeriesAt.congr (Filter.eventuallyEq_of_mem (ball_mem_nhds 0 hs0) heq)`. Establish `hR0 : 0 < (‖X‖ + ρ) / 2` using `by positivity`. Use `set R : NNReal := ⟨(‖X‖ + ρ) / 2, hR0.le⟩ with hRdef`. Establish `hR : 0 < R` using `by rw [← NNReal.coe_pos]; exact hR0`. Establish `hdR : DifferentiableOn ℂ Q (closedBall 0 R)` using `hQ.mono (closedBall_subset_ball (by change (‖X‖ + ρ) / 2 < ρ; linarith))`.

Establish `hC` using `hdR.hasFPowerSeriesOnBall hR`. Establish `hCp : cauchyPowerSeries Q 0 R = p` using `hC.hasFPowerSeriesAt.eq_formalMultilinearSeries hQp`. Rewrite `hC` using `[hCp]`. Establish `hXm : X ∈ EMetric.ball (0 : ℂ) R`. Express the relevant statement in the definitionally equal form `edist _ (0 : ℂ) < _`.

Rewrite using `[edist_zero_right]`. Conclude with `ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; change ‖X‖ < (‖X‖ + ρ) / 2; linarith)`. Use `hC.hasSum hXm` as an intermediate fact. Simplify using `only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at this`. Conclude with `this`.
-/
theorem gradedSeries_continue {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (δ ρ : ℝ) (Q : ℂ → ℂ)
    (hδ : 0 < δ) (hQ : DifferentiableOn ℂ Q (ball 0 ρ))
    (h : ∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => c i * (x : ℂ) ^ deg i) (Q x))
    (X : ℂ) (hX : ‖X‖ < ρ) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * X ^ k) (Q X) := by
  set A : ℕ → ℂ := fun k => ∑' i : deg ⁻¹' {k}, c i with hAdef
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ A with hpdef
  have hx0 : 0 < δ / 2 := by positivity
  set x0 : NNReal := ⟨δ / 2, hx0.le⟩ with hx0def
  have hrad : (x0 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    have hs := (gradedSeries_regroup deg c _ _ (h (δ / 2) hx0 (by linarith))).summable
    have hs' := summable_norm_iff.mpr hs
    refine hs'.congr fun n => ?_
    simp only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx0]
    rfl
  have hF := p.hasFPowerSeriesOnBall (lt_of_lt_of_le (ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos]; exact hx0)) hrad)
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hX
  have hs0 : 0 < min (δ / 2) ρ := lt_min hx0 hρ
  have hQan : AnalyticOnNhd ℂ Q (ball 0 ρ) := hQ.analyticOnNhd isOpen_ball
  have hmem : ∀ z : ℂ, ‖z‖ < δ / 2 → z ∈ EMetric.ball (0 : ℂ) p.radius := by
    intro z hz
    change edist _ (0 : ℂ) < _
    rw [edist_zero_right]
    refine lt_of_lt_of_le ?_ hrad
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; exact hz)
  have hFan : AnalyticOnNhd ℂ p.sum (ball 0 (min (δ / 2) ρ)) := fun z hz =>
    hF.analyticAt_of_mem (hmem z (lt_of_lt_of_le (by simpa using hz) (min_le_left _ _)))
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using (ne_of_gt hx))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), p.sum z = Q z := by
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT hx0] with x hx
    have h1 := gradedSeries_regroup deg c _ _ (h x hx.1 (by linarith [hx.2]))
    simp only [p, FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
    exact h1.tsum_eq
  have heq : EqOn p.sum Q (ball 0 (min (δ / 2) ρ)) :=
    hFan.eqOn_of_preconnected_of_frequently_eq
      (hQan.mono (ball_subset_ball (min_le_right _ _)))
      (convex_ball _ _).isPreconnected (mem_ball_self hs0) hfreq
  have hQp : HasFPowerSeriesAt Q p 0 :=
    hF.hasFPowerSeriesAt.congr (Filter.eventuallyEq_of_mem (ball_mem_nhds 0 hs0) heq)
  have hR0 : 0 < (‖X‖ + ρ) / 2 := by positivity
  set R : NNReal := ⟨(‖X‖ + ρ) / 2, hR0.le⟩ with hRdef
  have hR : 0 < R := by rw [← NNReal.coe_pos]; exact hR0
  have hdR : DifferentiableOn ℂ Q (closedBall 0 R) :=
    hQ.mono (closedBall_subset_ball (by change (‖X‖ + ρ) / 2 < ρ; linarith))
  have hC := hdR.hasFPowerSeriesOnBall hR
  have hCp : cauchyPowerSeries Q 0 R = p := hC.hasFPowerSeriesAt.eq_formalMultilinearSeries hQp
  rw [hCp] at hC
  have hXm : X ∈ EMetric.ball (0 : ℂ) R := by
    change edist _ (0 : ℂ) < _
    rw [edist_zero_right]
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; change ‖X‖ < (‖X‖ + ρ) / 2; linarith)
  have := hC.hasSum hXm
  simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at this
  exact this

/- English proof (translation)
Introduce `ι deg hfin a b C δ ρ P P' hδ hb hab hP hP' h X hX`. Establish `hA` using `gradedSeries_continue deg a δ ρ P hδ hP (fun x h1 h2 => (h x h1 h2).1) X hX`. Establish `hB` using `gradedSeries_continue deg (fun i => (b i : ℂ)) δ ρ P' hδ hP' (fun x h1 h2 => (h x h1 h2).2) ((‖X‖ : ℝ) : ℂ) (by simpa using hX)`. Establish `hBr : Summable (fun k => (∑' i : deg ⁻¹' {k}, b i) * ‖X‖ ^ k)`. Rewrite using `[← Complex.summable_ofReal]`.

Use `hB.summable.congr fun k => ?_` and prove the remaining obligations. Move the coercions through the operations in `[Complex.ofReal_tsum]`. Both sides reduce to the same expression. Establish `hsb : Summable (fun i => b i * ‖X‖ ^ deg i)`. Rewrite using `[← (Equiv.sigmaFiberEquiv deg).summable_iff]`.

Rewrite using `[summable_sigma_of_nonneg (f := (fun i => b i * ‖X‖ ^ deg i) ∘ (Equiv.sigmaFiberEquiv deg)) (fun _ => mul_nonneg (hb _) (pow_nonneg (norm_nonneg _) _))]`. Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Establish `: Finite {i // deg i = k}` using `(hfin k).to_subtype`. Conclude with `Summable.of_finite`. Use `hBr.congr fun k => ?_` and prove the remaining obligations.

Rewrite using `[← tsum_mul_right]`. Conclude with `tsum_congr fun y => by`. Simplify using `[Equiv.sigmaFiberEquiv, show deg y.1 = k from y.2]`. Establish `hsa : Summable (fun i => a i * X ^ deg i)`. Use `Summable.of_norm_bounded (hsb.mul_left C) fun i => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_pow, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (hab i) (pow_nonneg (norm_nonneg _) _)`. Use `⟨?_, hsb⟩` and prove the remaining obligations. Establish `h3` using `hsa.hasSum`. Establish `h4` using `(gradedSeries_regroup deg a X _ h3).unique hA`.

Rewrite `h3` using `[h4]`. Conclude with `h3`.
-/
theorem gradedSeries_continuation_dominated : ∀ {ι : Type} (deg : ι → ℕ),
    (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ),
    0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) →
    DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) →
    (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧
      HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) →
    ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧
      Summable (fun i => b i * ‖X‖ ^ deg i) := by
  intro ι deg hfin a b C δ ρ P P' hδ hb hab hP hP' h X hX
  have hA := gradedSeries_continue deg a δ ρ P hδ hP (fun x h1 h2 => (h x h1 h2).1) X hX
  have hB := gradedSeries_continue deg (fun i => (b i : ℂ)) δ ρ P' hδ hP'
    (fun x h1 h2 => (h x h1 h2).2) ((‖X‖ : ℝ) : ℂ) (by simpa using hX)
  have hBr : Summable (fun k => (∑' i : deg ⁻¹' {k}, b i) * ‖X‖ ^ k) := by
    rw [← Complex.summable_ofReal]
    refine hB.summable.congr fun k => ?_
    push_cast [Complex.ofReal_tsum]
    rfl
  have hsb : Summable (fun i => b i * ‖X‖ ^ deg i) := by
    rw [← (Equiv.sigmaFiberEquiv deg).summable_iff]
    rw [summable_sigma_of_nonneg (f := (fun i => b i * ‖X‖ ^ deg i) ∘ (Equiv.sigmaFiberEquiv deg))
      (fun _ => mul_nonneg (hb _) (pow_nonneg (norm_nonneg _) _))]
    refine ⟨fun k => ?_, ?_⟩
    · have : Finite {i // deg i = k} := (hfin k).to_subtype
      exact Summable.of_finite
    · refine hBr.congr fun k => ?_
      rw [← tsum_mul_right]
      exact tsum_congr fun y => by
        simp [Equiv.sigmaFiberEquiv, show deg y.1 = k from y.2]
  have hsa : Summable (fun i => a i * X ^ deg i) := by
    refine Summable.of_norm_bounded (hsb.mul_left C) fun i => ?_
    rw [norm_mul, norm_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hab i) (pow_nonneg (norm_nonneg _) _)
  refine ⟨?_, hsb⟩
  have h3 := hsa.hasSum
  have h4 := (gradedSeries_regroup deg a X _ h3).unique hA
  rw [h4] at h3
  exact h3

end GlobalTheory
