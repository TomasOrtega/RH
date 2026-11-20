import Mathlib

open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Establish `hr : 0 < r` using `lt_of_le_of_lt hx0 hxr`. Use `set t0 : ℝ := ε / 2 with ht0`. Establish `ht0pos : 0 < t0` using `by positivity`. Establish `ht0ε : t0 < ε` using `by linarith`. Establish `hnt0 : ‖(t0 : ℂ)‖ = t0` using `by simp [abs_of_pos ht0pos]`.

Establish `hsum0 : Summable (fun i => c i * t0 ^ n i)`. Establish `h` using `(hser (t0 : ℂ) (by rw [hnt0]; exact ht0pos) (by rw [hnt0]; exact ht0ε)).summable`. Establish `e : (fun i => (c i : ℂ) * (t0 : ℂ) ^ n i) = fun i => ((c i * t0 ^ n i : ℝ) : ℂ)`. Use function extensionality and compare the values at `i`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite `h` using `[e]`. Conclude with `Complex.summable_ofReal.mp h`. Establish `hfib : ∀ m : ℕ, Summable (fun i : n ⁻¹' {m} => c i)`. Introduce `m`.

Establish `h1` using `(hsum0.subtype (n ⁻¹' {m})).mul_right (t0 ^ m)⁻¹`. Use `h1.congr fun i => ?_` and prove the remaining obligations. Establish `hi : n i.val = m` using `i.2`. Simplify using `only [Function.comp_apply]`. Rewrite using `[hi, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0pos.ne'), mul_one]`.

Use `set C : ℕ → ℝ := fun m => ∑' i : n ⁻¹' {m}, c i with hC`. Establish `hCnn : ∀ m, 0 ≤ C m` using `fun m => tsum_nonneg (fun i => hc i)`. Establish `hgroup : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun m => (C m : ℂ) * z ^ m) (R z)`. Introduce `z hz1 hz2`. Use `((hser z hz1 hz2).tsum_fiberwise n).congr_fun fun m => ?_` and prove the remaining obligations.

Establish `e1 : (∑' i : n ⁻¹' {m}, (c i : ℂ) * z ^ n i) = ∑' i : n ⁻¹' {m}, (c i : ℂ) * z ^ m` using `tsum_congr fun i => by rw [show n i = m from i.2]`. Rewrite using `[e1, tsum_mul_right, hC, Complex.ofReal_tsum]`. Establish `hCt0 : Summable (fun m => C m * t0 ^ m)`. Establish `h` using `(hgroup (t0 : ℂ) (by rw [hnt0]; exact ht0pos) (by rw [hnt0]; exact ht0ε)).summable`. Establish `e : (fun m => (C m : ℂ) * (t0 : ℂ) ^ m) = fun m => ((C m * t0 ^ m : ℝ) : ℂ)`.

Use function extensionality and compare the values at `m`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `h` using `[e]`. Conclude with `Complex.summable_ofReal.mp h`.

Use `set q : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun m => (C m : ℂ)) with hq`. Establish `hqapply : ∀ (m : ℕ) (z : ℂ), q m (fun _ => z) = (C m : ℂ) * z ^ m`. Introduce `m z`. Rewrite using `[hq, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]`. Use `set t0n : NNReal := ⟨t0, ht0pos.le⟩ with ht0n`.

Establish `hrad : (t0n : ENNReal) ≤ q.radius`. Use `q.le_radius_of_bound (∑' m, C m * t0 ^ m) fun m => ?_` and prove the remaining obligations. Rewrite using `[show ((t0n : ℝ)) = t0 from rfl]`. Establish `hn : ‖q m‖ = C m`. Rewrite using `[hq, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hCnn m)]`.

Rewrite using `[hn]`. Conclude with `hCt0.le_tsum m (fun j _ => mul_nonneg (hCnn j) (pow_nonneg ht0pos.le _))`. Establish `hradpos : 0 < q.radius` using `lt_of_lt_of_le (ENNReal.coe_pos.mpr (NNReal.coe_pos.mp (show (0:ℝ) < (t0n : ℝ) from ht0pos))) hrad`. Establish `hqball` using `q.hasFPowerSeriesOnBall hradpos`. Establish `hRan : AnalyticAt ℂ R 0` using `hR.analyticAt (Metric.ball_mem_nhds 0 hr)`.

Establish `hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), R z = q.sum z`. Apply `Eventually.frequently` to reduce the goal to its premises. Establish `hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball (0 : ℂ) ε` using `nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hε)`. Use `filter_upwards [hb, self_mem_nhdsWithin] with z hz hz0`. Establish `hz0' : 0 < ‖z‖` using `norm_pos_iff.mpr hz0`.

Rewrite `hz` using `[mem_ball_zero_iff]`. Rewrite using `[FormalMultilinearSeries.sum]`. Repeatedly rewrite using `[hqapply]`. Conclude with `((hgroup z hz0' hz).tsum_eq).symm`. Establish `hev` using `(hRan.frequently_eq_iff_eventually_eq hqball.analyticAt).mp hfreq`.

Establish `hRq : HasFPowerSeriesAt R q 0` using `hqball.hasFPowerSeriesAt.congr (hev.mono fun z h => h.symm)`. Use `set ρ : ℝ := (x + r) / 2 with hρ`. Establish `hρpos : 0 < ρ` using `by linarith`. Use `set ρn : NNReal := ⟨ρ, hρpos.le⟩ with hρn`. Establish `hcl : DifferentiableOn ℂ R (Metric.closedBall 0 (ρn : ℝ))` using `hR.mono (Metric.closedBall_subset_ball (by show ρ < r; linarith))`.

Establish `hp` using `hcl.hasFPowerSeriesOnBall (by exact_mod_cast hρpos)`. Establish `hpq` using `hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hRq`. Rewrite `hp` using `[hpq]`. Establish `hxn : ‖(x : ℂ)‖₊ < ρn`. Rewrite using `[← NNReal.coe_lt_coe, coe_nnnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]`.

Use `show x < ρ`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hxmem : (x : ℂ) ∈ EMetric.ball (0 : ℂ) (ρn : ENNReal)` using `by show edist (x : ℂ) 0 < ρn`. Rewrite using `[edist_zero_right, enorm_eq_nnnorm]`. Conclude with `hxn` after adjusting the coercions.

Establish `hsx` using `(hp.hasSum hxmem).summable`. Rewrite `hsx` using `[hqapply]`. Establish `hCx : Summable (fun m => C m * x ^ m)`. Establish `e : (fun m => (C m : ℂ) * (x : ℂ) ^ m) = fun m => ((C m * x ^ m : ℝ) : ℂ)`. Use function extensionality and compare the values at `m`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite `hsx` using `[e]`. Conclude with `Complex.summable_ofReal.mp hsx`. Rewrite using `[← (Equiv.sigmaFiberEquiv n).summable_iff]`.

Use `(summable_sigma_of_nonneg fun p => ?_).mpr ⟨fun m => ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_nonneg (hc _) (pow_nonneg hx0 _)`. Use `((hfib m).mul_right (x ^ m)).congr fun i => ?_` and prove the remaining obligations. Simplify using `[Equiv.sigmaFiberEquiv, show n i = m from i.2]`. Use `hCx.congr fun m => ?_` and prove the remaining obligations.

Establish `e1 : (∑' i : {i // n i = m}, ((fun i => c i * x ^ n i) ∘ (Equiv.sigmaFiberEquiv n)) ⟨m, i⟩) = ∑' i : n ⁻¹' {m}, c i * x ^ m` using `tsum_congr fun i => by simp [Equiv.sigmaFiberEquiv, show n i = m from i.2]`. Rewrite using `[e1, tsum_mul_right]`.
-/
theorem summable_nonneg_family_of_differentiableOn {ι : Type} (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ) (hc : ∀ i, 0 ≤ c i) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hser : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => (c i : ℂ) * z ^ n i) (R z))
    (x : ℝ) (hx0 : 0 ≤ x) (hxr : x < r) : Summable (fun i => c i * x ^ n i) := by
  have hr : 0 < r := lt_of_le_of_lt hx0 hxr
  set t0 : ℝ := ε / 2 with ht0
  have ht0pos : 0 < t0 := by positivity
  have ht0ε : t0 < ε := by linarith
  have hnt0 : ‖(t0 : ℂ)‖ = t0 := by simp [abs_of_pos ht0pos]
  have hsum0 : Summable (fun i => c i * t0 ^ n i) := by
    have h := (hser (t0 : ℂ) (by rw [hnt0]; exact ht0pos) (by rw [hnt0]; exact ht0ε)).summable
    have e : (fun i => (c i : ℂ) * (t0 : ℂ) ^ n i) = fun i => ((c i * t0 ^ n i : ℝ) : ℂ) := by
      funext i; push_cast; rfl
    rw [e] at h
    exact Complex.summable_ofReal.mp h
  have hfib : ∀ m : ℕ, Summable (fun i : n ⁻¹' {m} => c i) := by
    intro m
    have h1 := (hsum0.subtype (n ⁻¹' {m})).mul_right (t0 ^ m)⁻¹
    refine h1.congr fun i => ?_
    have hi : n i.val = m := i.2
    simp only [Function.comp_apply]
    rw [hi, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0pos.ne'), mul_one]
  set C : ℕ → ℝ := fun m => ∑' i : n ⁻¹' {m}, c i with hC
  have hCnn : ∀ m, 0 ≤ C m := fun m => tsum_nonneg (fun i => hc i)
  have hgroup : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun m => (C m : ℂ) * z ^ m) (R z) := by
    intro z hz1 hz2
    refine ((hser z hz1 hz2).tsum_fiberwise n).congr_fun fun m => ?_
    have e1 : (∑' i : n ⁻¹' {m}, (c i : ℂ) * z ^ n i) = ∑' i : n ⁻¹' {m}, (c i : ℂ) * z ^ m :=
      tsum_congr fun i => by rw [show n i = m from i.2]
    rw [e1, tsum_mul_right, hC, Complex.ofReal_tsum]
  have hCt0 : Summable (fun m => C m * t0 ^ m) := by
    have h := (hgroup (t0 : ℂ) (by rw [hnt0]; exact ht0pos) (by rw [hnt0]; exact ht0ε)).summable
    have e : (fun m => (C m : ℂ) * (t0 : ℂ) ^ m) = fun m => ((C m * t0 ^ m : ℝ) : ℂ) := by
      funext m; push_cast; rfl
    rw [e] at h
    exact Complex.summable_ofReal.mp h
  set q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun m => (C m : ℂ)) with hq
  have hqapply : ∀ (m : ℕ) (z : ℂ), q m (fun _ => z) = (C m : ℂ) * z ^ m := by
    intro m z; rw [hq, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  set t0n : NNReal := ⟨t0, ht0pos.le⟩ with ht0n
  have hrad : (t0n : ENNReal) ≤ q.radius := by
    refine q.le_radius_of_bound (∑' m, C m * t0 ^ m) fun m => ?_
    rw [show ((t0n : ℝ)) = t0 from rfl]
    have hn : ‖q m‖ = C m := by
      rw [hq, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hCnn m)]
    rw [hn]
    exact hCt0.le_tsum m (fun j _ => mul_nonneg (hCnn j) (pow_nonneg ht0pos.le _))
  have hradpos : 0 < q.radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr (NNReal.coe_pos.mp (show (0:ℝ) < (t0n : ℝ) from ht0pos))) hrad
  have hqball := q.hasFPowerSeriesOnBall hradpos
  have hRan : AnalyticAt ℂ R 0 := hR.analyticAt (Metric.ball_mem_nhds 0 hr)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), R z = q.sum z := by
    apply Eventually.frequently
    have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball (0 : ℂ) ε :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hb, self_mem_nhdsWithin] with z hz hz0
    have hz0' : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [mem_ball_zero_iff] at hz
    rw [FormalMultilinearSeries.sum]
    simp_rw [hqapply]
    exact ((hgroup z hz0' hz).tsum_eq).symm
  have hev := (hRan.frequently_eq_iff_eventually_eq hqball.analyticAt).mp hfreq
  have hRq : HasFPowerSeriesAt R q 0 := hqball.hasFPowerSeriesAt.congr (hev.mono fun z h => h.symm)
  set ρ : ℝ := (x + r) / 2 with hρ
  have hρpos : 0 < ρ := by linarith
  set ρn : NNReal := ⟨ρ, hρpos.le⟩ with hρn
  have hcl : DifferentiableOn ℂ R (Metric.closedBall 0 (ρn : ℝ)) :=
    hR.mono (Metric.closedBall_subset_ball (by show ρ < r; linarith))
  have hp := hcl.hasFPowerSeriesOnBall (by exact_mod_cast hρpos)
  have hpq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hRq
  rw [hpq] at hp
  have hxn : ‖(x : ℂ)‖₊ < ρn := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    show x < ρ
    linarith
  have hxmem : (x : ℂ) ∈ EMetric.ball (0 : ℂ) (ρn : ENNReal) := by
    show edist (x : ℂ) 0 < ρn
    rw [edist_zero_right, enorm_eq_nnnorm]
    exact_mod_cast hxn
  have hsx := (hp.hasSum hxmem).summable
  simp_rw [hqapply] at hsx
  have hCx : Summable (fun m => C m * x ^ m) := by
    have e : (fun m => (C m : ℂ) * (x : ℂ) ^ m) = fun m => ((C m * x ^ m : ℝ) : ℂ) := by
      funext m; push_cast; rfl
    rw [e] at hsx
    exact Complex.summable_ofReal.mp hsx
  rw [← (Equiv.sigmaFiberEquiv n).summable_iff]
  refine (summable_sigma_of_nonneg fun p => ?_).mpr ⟨fun m => ?_, ?_⟩
  · exact mul_nonneg (hc _) (pow_nonneg hx0 _)
  · refine ((hfib m).mul_right (x ^ m)).congr fun i => ?_
    simp [Equiv.sigmaFiberEquiv, show n i = m from i.2]
  · refine hCx.congr fun m => ?_
    have e1 : (∑' i : {i // n i = m}, ((fun i => c i * x ^ n i) ∘ (Equiv.sigmaFiberEquiv n))
        ⟨m, i⟩) = ∑' i : n ⁻¹' {m}, c i * x ^ m :=
      tsum_congr fun i => by simp [Equiv.sigmaFiberEquiv, show n i = m from i.2]
    rw [e1, tsum_mul_right]

end GlobalTheory
