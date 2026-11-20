import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

open Filter Topology Metric
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.PoleBound

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `u hc hd _`. Conclude with `⟨u, hc, hd, fun z _ _ => by simp⟩`.

Consider the case `succ r ih`. Introduce `u hc hd hb`. Take `⟨B, hB⟩` from `hb`. Establish `hdiff : DifferentiableAt ℂ u (s₀ : ℂ)` using `hd.differentiableAt (ball_mem_nhds _ hε)`. Establish `hu0 : u (s₀ : ℂ) = 0`.

Establish `hlim₁ : Tendsto (fun σ : ℝ => u (σ : ℂ)) (𝓝[>] s₀) (𝓝 (u (s₀ : ℂ)))` using `((hdiff.continuousAt.tendsto).comp (Complex.continuous_ofReal.tendsto s₀)).mono_left nhdsWithin_le_nhds`. Establish `hsmall : Tendsto (fun σ : ℝ => B * ‖(σ : ℂ) - s₀‖ ^ (r + 1)) (𝓝[>] s₀) (𝓝 0)`. Establish `hcont : Continuous (fun σ : ℝ => B * ‖(σ : ℂ) - s₀‖ ^ (r + 1))` using `by fun_prop`. Simplify using `using (hcont.tendsto s₀).mono_left nhdsWithin_le_nhds`. Establish `hlim₂ : Tendsto (fun σ : ℝ => u (σ : ℂ)) (𝓝[>] s₀) (𝓝 0)`.

Use `squeeze_zero_norm' ?_ hsmall` and prove the remaining obligations. Use `filter_upwards [hB, self_mem_nhdsWithin] with σ hσB hσ`. Establish `hne : ((σ : ℂ) - s₀) ^ (r + 1) ≠ 0` using `pow_ne_zero _ (sub_ne_zero.mpr (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne'))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← norm_pow, ← norm_mul, div_mul_cancel₀ _ hne]`.

Use `_ ≤ B * ‖(σ : ℂ) - s₀‖ ^ (r + 1) := mul_le_mul_of_nonneg_right hσB (pow_nonneg (norm_nonneg _) _)`. Conclude with `tendsto_nhds_unique hlim₁ hlim₂`. Establish `huv : ∀ z, u z = (z - s₀) * dslope u (s₀ : ℂ) z`. Introduce `z`. Establish `h` using `sub_smul_dslope u (s₀ : ℂ) z`.

Rewrite `h` using `[hu0, sub_zero, smul_eq_mul]`. Conclude with `h.symm`. Establish `hvc : ContinuousOn (dslope u (s₀ : ℂ)) (closedBall (s₀ : ℂ) ε)`. Introduce `z hz`. Distinguish the cases in `hzs : z = s₀`.

Substitute `hzs` using the available equality. Conclude with `(continuousAt_dslope_same.mpr hdiff).continuousWithinAt`. Conclude with `(continuousWithinAt_dslope_of_ne hzs).mpr (hc z hz)`. Establish `hvd : DifferentiableOn ℂ (dslope u (s₀ : ℂ)) (ball (s₀ : ℂ) ε)` using `(Complex.differentiableOn_dslope (ball_mem_nhds _ hε)).mpr hd`. Establish `hvb : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖dslope u (s₀ : ℂ) (σ : ℂ) / ((σ : ℂ) - s₀) ^ r‖ ≤ B`.

Use `⟨B, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hB, self_mem_nhdsWithin] with σ hσB hσ`. Establish `hne : (σ : ℂ) - s₀ ≠ 0` using `sub_ne_zero.mpr (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne')`. Rewrite `hσB` using `[huv (σ : ℂ), pow_succ, mul_comm ((σ : ℂ) - s₀) (dslope u (s₀ : ℂ) (σ : ℂ)), mul_div_mul_right _ _ hne]`. Then use the resulting hypothesis. Take `⟨w, hwc, hwd, hw⟩` from `ih (dslope u (s₀ : ℂ)) hvc hvd hvb`.

Use `⟨w, hwc, hwd, fun z hz hzs => ?_⟩` and prove the remaining obligations. Rewrite using `[huv z, hw z hz hzs, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem factor_of_real_bound (s₀ ε : ℝ) (hε : 0 < ε) :
    ∀ (r : ℕ) (u : ℂ → ℂ), ContinuousOn u (closedBall (s₀ : ℂ) ε) →
      DifferentiableOn ℂ u (ball (s₀ : ℂ) ε) →
      (∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖u (σ : ℂ) / ((σ : ℂ) - s₀) ^ r‖ ≤ B) →
      ∃ w : ℂ → ℂ, ContinuousOn w (closedBall (s₀ : ℂ) ε) ∧
        DifferentiableOn ℂ w (ball (s₀ : ℂ) ε) ∧
        ∀ z ∈ closedBall (s₀ : ℂ) ε, z ≠ s₀ → u z = (z - s₀) ^ r * w z := by
  intro r
  induction r with
  | zero =>
    intro u hc hd _
    exact ⟨u, hc, hd, fun z _ _ => by simp⟩
  | succ r ih =>
    intro u hc hd hb
    obtain ⟨B, hB⟩ := hb
    have hdiff : DifferentiableAt ℂ u (s₀ : ℂ) := hd.differentiableAt (ball_mem_nhds _ hε)
    have hu0 : u (s₀ : ℂ) = 0 := by
      have hlim₁ : Tendsto (fun σ : ℝ => u (σ : ℂ)) (𝓝[>] s₀) (𝓝 (u (s₀ : ℂ))) :=
        ((hdiff.continuousAt.tendsto).comp (Complex.continuous_ofReal.tendsto s₀)).mono_left
          nhdsWithin_le_nhds
      have hsmall : Tendsto (fun σ : ℝ => B * ‖(σ : ℂ) - s₀‖ ^ (r + 1)) (𝓝[>] s₀) (𝓝 0) := by
        have hcont : Continuous (fun σ : ℝ => B * ‖(σ : ℂ) - s₀‖ ^ (r + 1)) := by fun_prop
        simpa using (hcont.tendsto s₀).mono_left nhdsWithin_le_nhds
      have hlim₂ : Tendsto (fun σ : ℝ => u (σ : ℂ)) (𝓝[>] s₀) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ hsmall
        filter_upwards [hB, self_mem_nhdsWithin] with σ hσB hσ
        have hne : ((σ : ℂ) - s₀) ^ (r + 1) ≠ 0 :=
          pow_ne_zero _ (sub_ne_zero.mpr (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne'))
        calc ‖u (σ : ℂ)‖ = ‖u (σ : ℂ) / ((σ : ℂ) - s₀) ^ (r + 1)‖ * ‖(σ : ℂ) - s₀‖ ^ (r + 1) := by
              rw [← norm_pow, ← norm_mul, div_mul_cancel₀ _ hne]
          _ ≤ B * ‖(σ : ℂ) - s₀‖ ^ (r + 1) :=
              mul_le_mul_of_nonneg_right hσB (pow_nonneg (norm_nonneg _) _)
      exact tendsto_nhds_unique hlim₁ hlim₂
    have huv : ∀ z, u z = (z - s₀) * dslope u (s₀ : ℂ) z := by
      intro z
      have h := sub_smul_dslope u (s₀ : ℂ) z
      rw [hu0, sub_zero, smul_eq_mul] at h
      exact h.symm
    have hvc : ContinuousOn (dslope u (s₀ : ℂ)) (closedBall (s₀ : ℂ) ε) := by
      intro z hz
      by_cases hzs : z = s₀
      · subst hzs
        exact (continuousAt_dslope_same.mpr hdiff).continuousWithinAt
      · exact (continuousWithinAt_dslope_of_ne hzs).mpr (hc z hz)
    have hvd : DifferentiableOn ℂ (dslope u (s₀ : ℂ)) (ball (s₀ : ℂ) ε) :=
      (Complex.differentiableOn_dslope (ball_mem_nhds _ hε)).mpr hd
    have hvb : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
        ‖dslope u (s₀ : ℂ) (σ : ℂ) / ((σ : ℂ) - s₀) ^ r‖ ≤ B := by
      refine ⟨B, ?_⟩
      filter_upwards [hB, self_mem_nhdsWithin] with σ hσB hσ
      have hne : (σ : ℂ) - s₀ ≠ 0 :=
        sub_ne_zero.mpr (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne')
      rwa [huv (σ : ℂ), pow_succ, mul_comm ((σ : ℂ) - s₀) (dslope u (s₀ : ℂ) (σ : ℂ)),
        mul_div_mul_right _ _ hne] at hσB
    obtain ⟨w, hwc, hwd, hw⟩ := ih (dslope u (s₀ : ℂ)) hvc hvd hvb
    refine ⟨w, hwc, hwd, fun z hz hzs => ?_⟩
    rw [huv z, hw z hz hzs, pow_succ]
    ring

/- English proof (translation)
Take `⟨q, hdq, hndvd⟩` from `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd0 (s₀ : ℂ)`. Use `set m := Polynomial.rootMultiplicity (s₀ : ℂ) d`. Establish `hdeval : ∀ z, d.eval z = (z - s₀) ^ m * q.eval z`. Introduce `z`. Use `conv_lhs => rw [hdq]`.

Simplify using the standard rewrite rules. Establish `hq : ∀ z ∈ closedBall (s₀ : ℂ) ε, q.eval z ≠ 0`. Introduce `z hz`. Distinguish the cases in `hzs : z = s₀`. Substitute `hzs` using the available equality.

Introduce `h0`. Conclude with `hndvd (Polynomial.dvd_iff_isRoot.mpr h0)`. Introduce `h0`. Conclude with `hne z hz hzs (by rw [hdeval, h0, mul_zero])`. Establish `hkey : ∀ z, (z - s₀) ^ n * (h z / d.eval z) = ((z - s₀) ^ n * h z / q.eval z) / (z - s₀) ^ m`.

Introduce `z`. Rewrite using `[hdeval]`. Simplify using `only [div_eq_mul_inv, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hud : DifferentiableOn ℂ (fun z => (z - s₀) ^ n * h z / q.eval z) (closedBall (s₀ : ℂ) ε)`.

Establish `hnum : DifferentiableOn ℂ (fun z => (z - s₀) ^ n * h z) (closedBall (s₀ : ℂ) ε)` using `by fun_prop`. Conclude with `hnum.div q.differentiable.differentiableOn hq`. Take `⟨B, hB⟩` from `hb`. Establish `hub : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖((σ : ℂ) - s₀) ^ n * h (σ : ℂ) / q.eval (σ : ℂ) / ((σ : ℂ) - s₀) ^ m‖ ≤ B` using `⟨B, hB.mono fun σ hσ => by rwa [hkey] at hσ⟩`. Take `⟨w, hwc, hwd, hw⟩` from `GlobalTheory.CompanionTheory.PoleBound.factor_of_real_bound s₀ ε hε m (fun z => (z - s₀) ^ n * h z / q.eval z) hud.continuousOn (hud.mono ball_subset_closedBall) hub`.

Use `⟨w, hwc, hwd, fun z hz hzs => ?_⟩` and prove the remaining obligations. Rewrite using `[hkey z, hw z hz hzs, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hzs))]`.
-/
theorem extend_of_real_bound (h : ℂ → ℂ) (d : Polynomial ℂ) (s₀ ε : ℝ) (hε : 0 < ε) (hd0 : d ≠ 0)
    (hh : DifferentiableOn ℂ h (closedBall (s₀ : ℂ) ε))
    (hne : ∀ z ∈ closedBall (s₀ : ℂ) ε, z ≠ s₀ → d.eval z ≠ 0) (n : ℕ)
    (hb : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
      ‖((σ : ℂ) - s₀) ^ n * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B) :
    ∃ w : ℂ → ℂ, ContinuousOn w (closedBall (s₀ : ℂ) ε) ∧
      DifferentiableOn ℂ w (ball (s₀ : ℂ) ε) ∧
      ∀ z ∈ closedBall (s₀ : ℂ) ε, z ≠ s₀ → (z - s₀) ^ n * (h z / d.eval z) = w z := by
  obtain ⟨q, hdq, hndvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd0 (s₀ : ℂ)
  set m := Polynomial.rootMultiplicity (s₀ : ℂ) d
  have hdeval : ∀ z, d.eval z = (z - s₀) ^ m * q.eval z := by
    intro z
    conv_lhs => rw [hdq]
    simp
  have hq : ∀ z ∈ closedBall (s₀ : ℂ) ε, q.eval z ≠ 0 := by
    intro z hz
    by_cases hzs : z = s₀
    · subst hzs
      intro h0
      exact hndvd (Polynomial.dvd_iff_isRoot.mpr h0)
    · intro h0
      exact hne z hz hzs (by rw [hdeval, h0, mul_zero])
  have hkey : ∀ z, (z - s₀) ^ n * (h z / d.eval z) =
      ((z - s₀) ^ n * h z / q.eval z) / (z - s₀) ^ m := by
    intro z
    rw [hdeval]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hud : DifferentiableOn ℂ (fun z => (z - s₀) ^ n * h z / q.eval z)
      (closedBall (s₀ : ℂ) ε) := by
    have hnum : DifferentiableOn ℂ (fun z => (z - s₀) ^ n * h z) (closedBall (s₀ : ℂ) ε) := by
      fun_prop
    exact hnum.div q.differentiable.differentiableOn hq
  obtain ⟨B, hB⟩ := hb
  have hub : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
      ‖((σ : ℂ) - s₀) ^ n * h (σ : ℂ) / q.eval (σ : ℂ) / ((σ : ℂ) - s₀) ^ m‖ ≤ B :=
    ⟨B, hB.mono fun σ hσ => by rwa [hkey] at hσ⟩
  obtain ⟨w, hwc, hwd, hw⟩ := GlobalTheory.CompanionTheory.PoleBound.factor_of_real_bound s₀ ε hε m
    (fun z => (z - s₀) ^ n * h z / q.eval z) hud.continuousOn
    (hud.mono ball_subset_closedBall) hub
  refine ⟨w, hwc, hwd, fun z hz hzs => ?_⟩
  rw [hkey z, hw z hz hzs, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hzs))]

/- English proof (translation)
The claim follows from `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le Set.countable_empty hc fun _ hz => hd.differentiableAt (isOpen_ball.mem_nhds hz.1)`.
-/
theorem circle_zero (c : ℂ) (ε : ℝ) (hε : 0 < ε) (g : ℂ → ℂ) (hc : ContinuousOn g (closedBall c ε))
    (hd : DifferentiableOn ℂ g (ball c ε)) : (∮ z in C(c, ε), g z) = 0 :=
  Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le Set.countable_empty hc
    fun _ hz => hd.differentiableAt (isOpen_ball.mem_nhds hz.1)

/- English proof (translation)
Use `⟨sphere_subset_closedBall hz, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hz` using `[mem_sphere, dist_self]`. Conclude with `hε.ne hz`.
-/
theorem sphere_facts {c z : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : z ∈ sphere c ε) :
    z ∈ closedBall c ε ∧ z ≠ c := by
  refine ⟨sphere_subset_closedBall hz, ?_⟩
  rintro rfl
  rw [mem_sphere, dist_self] at hz
  exact hε.ne hz

/- English proof (translation)
Establish `hcongr : (∮ z in C(s₀, ε), (z - s₀) ^ (j + n) * f z) = ∮ z in C(s₀, ε), (z - s₀) ^ j * w z`. Use `circleIntegral.integral_congr hε.le fun z hz => ?_` and prove the remaining obligations. Take `⟨hzc, hzs⟩` from `GlobalTheory.CompanionTheory.PoleBound.sphere_facts hε hz`. Use `show (z - s₀) ^ (j + n) * f z = (z - s₀) ^ j * w z`. Rewrite using `[pow_add, mul_assoc, hw z hzc hzs]`.

Rewrite using `[hcongr]`. Use `GlobalTheory.CompanionTheory.PoleBound.circle_zero s₀ ε hε _ ?_ ?_` and prove the remaining obligations. Use `fun_prop`. Use `fun_prop`.
-/
theorem moment_zero (f w : ℂ → ℂ) (s₀ : ℂ) (ε : ℝ) (hε : 0 < ε) (n j : ℕ)
    (hwc : ContinuousOn w (closedBall s₀ ε)) (hwd : DifferentiableOn ℂ w (ball s₀ ε))
    (hw : ∀ z ∈ closedBall s₀ ε, z ≠ s₀ → (z - s₀) ^ n * f z = w z) :
    (∮ z in C(s₀, ε), (z - s₀) ^ (j + n) * f z) = 0 := by
  have hcongr : (∮ z in C(s₀, ε), (z - s₀) ^ (j + n) * f z) =
      ∮ z in C(s₀, ε), (z - s₀) ^ j * w z := by
    refine circleIntegral.integral_congr hε.le fun z hz => ?_
    obtain ⟨hzc, hzs⟩ := GlobalTheory.CompanionTheory.PoleBound.sphere_facts hε hz
    show (z - s₀) ^ (j + n) * f z = (z - s₀) ^ j * w z
    rw [pow_add, mul_assoc, hw z hzc hzs]
  rw [hcongr]
  refine GlobalTheory.CompanionTheory.PoleBound.circle_zero s₀ ε hε _ ?_ ?_
  · fun_prop
  · fun_prop

/- English proof (translation)
Introduce `h d s₀ ε hε hd0 hh _ hne`. Use `⟨fun hb => ?_, fun hb => ?_⟩` and prove the remaining obligations. Establish `hb' : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖((σ : ℂ) - s₀) ^ 1 * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B`. Take `⟨B, hB⟩` from `hb`. Conclude with `⟨B, hB.mono fun σ hσ => by rwa [pow_one, ← Complex.ofReal_sub]⟩`.

Take `⟨w, hwc, hwd, hw⟩` from `GlobalTheory.CompanionTheory.PoleBound.extend_of_real_bound h d s₀ ε hε hd0 hh hne 1 hb'`. Use `⟨fun k hk => ?_, ?_⟩` and prove the remaining obligations. Take `⟨j, rfl⟩ : ∃ j, k = j + 2` from `⟨k - 2, by omega⟩`. Establish `hj : j + 2 - 1 = j + 1` using `by omega`. Rewrite using `[hj]`.

Conclude with `GlobalTheory.CompanionTheory.PoleBound.moment_zero (fun z => h z / d.eval z) w (s₀ : ℂ) ε hε 1 j hwc hwd hw`. Establish `hint : (∮ z in C((s₀ : ℂ), ε), (z - s₀) ^ (1 - 1) * (h z / d.eval z)) = ∮ z in C((s₀ : ℂ), ε), (z - s₀)⁻¹ • w z`. Use `circleIntegral.integral_congr hε.le fun z hz => ?_` and prove the remaining obligations. Take `⟨hzc, hzs⟩` from `GlobalTheory.CompanionTheory.PoleBound.sphere_facts hε hz`. Use `show (z - s₀) ^ (1 - 1) * (h z / d.eval z) = (z - s₀)⁻¹ • w z`.

Rewrite using `[← hw z hzc hzs, smul_eq_mul, pow_one, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hzs), one_mul, Nat.sub_self, pow_zero, one_mul]`. Establish `hcauchy : (∮ z in C((s₀ : ℂ), ε), (z - s₀)⁻¹ • w z) = (2 * Real.pi * Complex.I : ℂ) • w s₀` using `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable Set.countable_empty (mem_ball_self hε) hwc fun x hx => hwd.differentiableAt (isOpen_ball.mem_nhds hx.1)`. Establish `h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero`. Rewrite using `[hint, hcauchy, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]`. Establish `hlim : Tendsto (fun σ : ℝ => w (σ : ℂ)) (𝓝[>] s₀) (𝓝 (w (s₀ : ℂ)))` using `(((hwc.continuousAt (closedBall_mem_nhds _ hε)).tendsto).comp (Complex.continuous_ofReal.tendsto s₀)).mono_left nhdsWithin_le_nhds`.

Use `Tendsto.congr' ?_ hlim` and prove the remaining obligations. Establish `hball : ∀ᶠ σ : ℝ in 𝓝[>] s₀, (σ : ℂ) ∈ closedBall (s₀ : ℂ) ε` using `nhdsWithin_le_nhds ((Complex.continuous_ofReal.tendsto s₀).eventually_mem (closedBall_mem_nhds _ hε))`. Use `filter_upwards [hball, self_mem_nhdsWithin] with σ hσb hσ`. Rewrite using `[← hw (σ : ℂ) hσb (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne'), pow_one, Complex.ofReal_sub]`. Establish `hb' : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖((σ : ℂ) - s₀) ^ 0 * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B`.

Take `⟨B, hB⟩` from `hb`. Conclude with `⟨B, hB.mono fun σ hσ => by rwa [pow_zero, one_mul]⟩`. Take `⟨w, hwc, hwd, hw⟩` from `GlobalTheory.CompanionTheory.PoleBound.extend_of_real_bound h d s₀ ε hε hd0 hh hne 0 hb'`. Introduce `k _`. Conclude with `GlobalTheory.CompanionTheory.PoleBound.moment_zero (fun z => h z / d.eval z) w (s₀ : ℂ) ε hε 0 (k - 1) hwc hwd hw`.
-/
theorem poleReal : PoleReal := by
  intro h d s₀ ε hε hd0 hh _ hne
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have hb' : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
        ‖((σ : ℂ) - s₀) ^ 1 * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B := by
      obtain ⟨B, hB⟩ := hb
      exact ⟨B, hB.mono fun σ hσ => by rwa [pow_one, ← Complex.ofReal_sub]⟩
    obtain ⟨w, hwc, hwd, hw⟩ := GlobalTheory.CompanionTheory.PoleBound.extend_of_real_bound h d s₀ ε hε hd0 hh hne 1 hb'
    refine ⟨fun k hk => ?_, ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hj : j + 2 - 1 = j + 1 := by omega
      rw [hj]
      exact GlobalTheory.CompanionTheory.PoleBound.moment_zero (fun z => h z / d.eval z) w (s₀ : ℂ) ε hε 1 j
        hwc hwd hw
    · have hint : (∮ z in C((s₀ : ℂ), ε), (z - s₀) ^ (1 - 1) * (h z / d.eval z)) =
          ∮ z in C((s₀ : ℂ), ε), (z - s₀)⁻¹ • w z := by
        refine circleIntegral.integral_congr hε.le fun z hz => ?_
        obtain ⟨hzc, hzs⟩ := GlobalTheory.CompanionTheory.PoleBound.sphere_facts hε hz
        show (z - s₀) ^ (1 - 1) * (h z / d.eval z) = (z - s₀)⁻¹ • w z
        rw [← hw z hzc hzs, smul_eq_mul, pow_one, ← mul_assoc,
          inv_mul_cancel₀ (sub_ne_zero.mpr hzs), one_mul, Nat.sub_self, pow_zero, one_mul]
      have hcauchy : (∮ z in C((s₀ : ℂ), ε), (z - s₀)⁻¹ • w z) =
          (2 * Real.pi * Complex.I : ℂ) • w s₀ :=
        Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          Set.countable_empty (mem_ball_self hε) hwc
          fun x hx => hwd.differentiableAt (isOpen_ball.mem_nhds hx.1)
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero
      rw [hint, hcauchy, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]
      have hlim : Tendsto (fun σ : ℝ => w (σ : ℂ)) (𝓝[>] s₀) (𝓝 (w (s₀ : ℂ))) :=
        (((hwc.continuousAt (closedBall_mem_nhds _ hε)).tendsto).comp
          (Complex.continuous_ofReal.tendsto s₀)).mono_left nhdsWithin_le_nhds
      refine Tendsto.congr' ?_ hlim
      have hball : ∀ᶠ σ : ℝ in 𝓝[>] s₀, (σ : ℂ) ∈ closedBall (s₀ : ℂ) ε :=
        nhdsWithin_le_nhds
          ((Complex.continuous_ofReal.tendsto s₀).eventually_mem (closedBall_mem_nhds _ hε))
      filter_upwards [hball, self_mem_nhdsWithin] with σ hσb hσ
      rw [← hw (σ : ℂ) hσb (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne'), pow_one,
        Complex.ofReal_sub]
  · have hb' : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
        ‖((σ : ℂ) - s₀) ^ 0 * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B := by
      obtain ⟨B, hB⟩ := hb
      exact ⟨B, hB.mono fun σ hσ => by rwa [pow_zero, one_mul]⟩
    obtain ⟨w, hwc, hwd, hw⟩ := GlobalTheory.CompanionTheory.PoleBound.extend_of_real_bound h d s₀ ε hε hd0 hh hne 0 hb'
    intro k _
    exact GlobalTheory.CompanionTheory.PoleBound.moment_zero (fun z => h z / d.eval z) w (s₀ : ℂ) ε hε 0
      (k - 1) hwc hwd hw

end GlobalTheory.CompanionTheory.PoleBound
