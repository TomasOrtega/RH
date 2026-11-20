import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `lam h0 hmul hc`. Establish `hcont : Continuous lam`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `t`. Establish `h1 : ContinuousAt (fun x => lam (x - t)) t`.

Apply `ContinuousAt.comp (g := lam) (f := fun x => x - t)` to reduce the goal to its premises. Simplify using `using hc`. Conclude with `(continuous_id.sub continuous_const).continuousAt`. Establish `h2 : (fun x => lam t * lam (x - t)) = lam`. Use function extensionality and compare the values at `x`.

Rewrite using `[← hmul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h2]`. Conclude with `continuousAt_const.mul h1`.

Use `set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, lam x with hF`. Establish `hFd : ∀ b, HasDerivAt F (lam b) b` using `fun b => (hcont.integral_hasStrictDerivAt 0 b).hasDerivAt`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by`. Use `(hFd 0).eventually_ne (c := 0) (by rw [h0]; exact one_ne_zero)` as an intermediate fact. Conclude with `this.exists`.

Establish `hi : ∀ a b : ℝ, IntervalIntegrable lam MeasureTheory.volume a b` using `fun a b => hcont.intervalIntegrable a b`. Establish `key : ∀ t, lam t * F δ = F (t + δ) - F t`. Introduce `t`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hF, hmul]`.

Rewrite using `[intervalIntegral.integral_const_mul]`. Use `_ = ∫ s in (t + 0)..(t + δ), lam s := intervalIntegral.integral_comp_add_left lam t`. Use `_ = F (t + δ) - F t := by`. Simplify using `only [add_zero, hF]`. Conclude with `(intervalIntegral.integral_interval_sub_left (hi 0 (t + δ)) (hi 0 t)).symm`.

Establish `hd : HasDerivAt (fun t => (F (t + δ) - F t) * (F δ)⁻¹) ((lam (0 + δ) - lam 0) * (F δ)⁻¹) 0`. Establish `h1 : HasDerivAt (fun t => F (t + δ)) (lam (0 + δ)) 0` using `HasDerivAt.comp_add_const 0 δ (hFd (0 + δ))`. Conclude with `(h1.sub (hFd 0)).mul_const _`. Use `⟨_, hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← key t, mul_assoc, mul_inv_cancel₀ hδ, mul_one]`.
-/
theorem multiplicative_hasDerivAt_zero : ∀ (lam : ℝ → ℂ), lam 0 = 1 →
    (∀ s t, lam (s + t) = lam s * lam t) → ContinuousAt lam 0 → ∃ c : ℂ, HasDerivAt lam c 0 := by
  intro lam h0 hmul hc
  have hcont : Continuous lam := by
    rw [continuous_iff_continuousAt]
    intro t
    have h1 : ContinuousAt (fun x => lam (x - t)) t := by
      apply ContinuousAt.comp (g := lam) (f := fun x => x - t)
      · simpa using hc
      · exact (continuous_id.sub continuous_const).continuousAt
    have h2 : (fun x => lam t * lam (x - t)) = lam := by
      funext x; rw [← hmul]; congr 1; ring
    rw [← h2]; exact continuousAt_const.mul h1
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, lam x with hF
  have hFd : ∀ b, HasDerivAt F (lam b) b := fun b =>
    (hcont.integral_hasStrictDerivAt 0 b).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    have := (hFd 0).eventually_ne (c := 0) (by rw [h0]; exact one_ne_zero)
    exact this.exists
  have hi : ∀ a b : ℝ, IntervalIntegrable lam MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have key : ∀ t, lam t * F δ = F (t + δ) - F t := by
    intro t
    calc lam t * F δ = ∫ s in (0:ℝ)..δ, lam (t + s) := by
          simp only [hF, hmul]; rw [intervalIntegral.integral_const_mul]
      _ = ∫ s in (t + 0)..(t + δ), lam s := intervalIntegral.integral_comp_add_left lam t
      _ = F (t + δ) - F t := by
          simp only [add_zero, hF]
          exact (intervalIntegral.integral_interval_sub_left (hi 0 (t + δ)) (hi 0 t)).symm
  have hd : HasDerivAt (fun t => (F (t + δ) - F t) * (F δ)⁻¹)
      ((lam (0 + δ) - lam 0) * (F δ)⁻¹) 0 := by
    have h1 : HasDerivAt (fun t => F (t + δ)) (lam (0 + δ)) 0 :=
      HasDerivAt.comp_add_const 0 δ (hFd (0 + δ))
    exact (h1.sub (hFd 0)).mul_const _
  refine ⟨_, hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)⟩
  simp only
  rw [← key t, mul_assoc, mul_inv_cancel₀ hδ, mul_one]

end GlobalTheory
