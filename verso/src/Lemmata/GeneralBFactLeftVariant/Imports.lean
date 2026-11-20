import Mathlib

namespace Bl.general_b_fact_left_variant

/- English proof (translation)
Introduce `f hf hmul h0 hnorm`. Establish `hFd : ∀ x : ℝ, HasDerivAt (fun u : ℝ => ∫ s in (0:ℝ)..u, f s) (f x) x` using `fun x => (hf.integral_hasStrictDerivAt 0 x).hasDerivAt`. Use `set F : ℝ → ℂ := fun u : ℝ => ∫ s in (0:ℝ)..u, f s with hF`. Establish `hF0 : F 0 = 0` using `by simp [hF]`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ⟩ : ∃ δ : ℝ, F δ ≠ 0 := by`.

Establish `h1 : ∀ᶠ z in nhdsWithin (0:ℝ) {0}ᶜ, F z ≠ 0` using `(hFd 0).eventually_ne (by rw [h0]; exact one_ne_zero)`. Take `⟨δ, hδ⟩` from `h1.exists`. Conclude with `⟨δ, hδ⟩`. Establish `key : ∀ t : ℝ, F (t + δ) - F t = f t * F δ`. Introduce `t`.

Simplify using `only [hF]`. Rewrite using `[intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _), ← intervalIntegral.integral_const_mul]`. Repeatedly rewrite using `[← hmul]`. Rewrite using `[intervalIntegral.integral_comp_add_left f t]`. Simplify using the standard rewrite rules.

Use `set c : ℂ := (f δ - 1) / F δ with hc`. Establish `hfd : ∀ t : ℝ, HasDerivAt f (c * f t) t`. Introduce `t`. Establish `hfe : ∀ u : ℝ, f u = (F (u + δ) - F u) / F δ`. Introduce `u`.

Rewrite using `[key u, mul_div_assoc, div_self hδ, mul_one]`. Establish `h2 : HasDerivAt (fun u => (F (u + δ) - F u) / F δ) ((f (t + δ) - f t) / F δ) t` using `((HasDerivAt.comp_add_const t δ (hFd (t + δ))).sub (hFd t)).div_const (F δ)`. Establish `h3` using `h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hfe)`. Establish `hv : (f (t + δ) - f t) / F δ = c * f t` using `by rw [hmul, hc]; ring`. Rewrite `h3` using `[hv]`. Then use the resulting hypothesis.

Establish `hg : ∀ t : ℝ, HasDerivAt (fun u : ℝ => f u * Complex.exp (-(c * (u:ℂ)))) 0 t`. Introduce `t`. Establish `he` using `(((hasDerivAt_id t).ofReal_comp).const_mul c).neg.cexp`. Establish `hm` using `(hfd t).mul he`. Conclude with `hm.congr_deriv (by simp only [id, Complex.ofReal_one, mul_one]; ring)`.

Establish `hconst : ∀ t : ℝ, f t * Complex.exp (-(c * (t:ℂ))) = 1`. Introduce `t`. Use `is_const_of_deriv_eq_zero (fun u => (hg u).differentiableAt) (fun u => (hg u).deriv) t 0` as an intermediate fact. Simplify `this` using `[h0]`. Establish `hexp : ∀ t : ℝ, f t = Complex.exp (c * t)`.

Introduce `t`. Establish `h3` using `hconst t`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← Complex.exp_add]`. Simplify using the standard rewrite rules.

Use `_ = Complex.exp (c * t) := by rw [h3, one_mul]`. Establish `hre : c.re = 0`. Establish `h4` using `hnorm 1`. Rewrite `h4` using `[hexp 1, Complex.norm_exp]`. Simplify using `using h4`.

Use `⟨c.im, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[hexp t]`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`.
-/
theorem goal1 :
  ∀ (f : Real → Complex),
  Continuous.{0, 0} f →
    (∀ (s t : Real), Eq.{1} (f (HAdd.hAdd.{0, 0, 0} s t)) (HMul.hMul.{0, 0, 0} (f s) (f t))) →
      Eq.{1} (f 0) 1 →
        (∀ (t : Real), Eq.{1} (Norm.norm.{0} (f t)) 1) →
          Exists.{1} fun (m : Real) ↦
            ∀ (t : Real),
              Eq.{1} (f t) (Complex.exp (HMul.hMul.{0, 0, 0} (Complex.ofReal (HMul.hMul.{0, 0, 0} m t)) Complex.I)) := by
  intro f hf hmul h0 hnorm
  have hFd : ∀ x : ℝ, HasDerivAt (fun u : ℝ => ∫ s in (0:ℝ)..u, f s) (f x) x :=
    fun x => (hf.integral_hasStrictDerivAt 0 x).hasDerivAt
  set F : ℝ → ℂ := fun u : ℝ => ∫ s in (0:ℝ)..u, f s with hF
  have hF0 : F 0 = 0 := by simp [hF]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, F δ ≠ 0 := by
    have h1 : ∀ᶠ z in nhdsWithin (0:ℝ) {0}ᶜ, F z ≠ 0 := (hFd 0).eventually_ne (by rw [h0]; exact one_ne_zero)
    obtain ⟨δ, hδ⟩ := h1.exists
    exact ⟨δ, hδ⟩
  have key : ∀ t : ℝ, F (t + δ) - F t = f t * F δ := by
    intro t
    simp only [hF]
    rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _), ← intervalIntegral.integral_const_mul]
    simp_rw [← hmul]
    rw [intervalIntegral.integral_comp_add_left f t]
    simp
  set c : ℂ := (f δ - 1) / F δ with hc
  have hfd : ∀ t : ℝ, HasDerivAt f (c * f t) t := by
    intro t
    have hfe : ∀ u : ℝ, f u = (F (u + δ) - F u) / F δ := by
      intro u; rw [key u, mul_div_assoc, div_self hδ, mul_one]
    have h2 : HasDerivAt (fun u => (F (u + δ) - F u) / F δ) ((f (t + δ) - f t) / F δ) t :=
      ((HasDerivAt.comp_add_const t δ (hFd (t + δ))).sub (hFd t)).div_const (F δ)
    have h3 := h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hfe)
    have hv : (f (t + δ) - f t) / F δ = c * f t := by rw [hmul, hc]; ring
    rwa [hv] at h3
  have hg : ∀ t : ℝ, HasDerivAt (fun u : ℝ => f u * Complex.exp (-(c * (u:ℂ)))) 0 t := by
    intro t
    have he := (((hasDerivAt_id t).ofReal_comp).const_mul c).neg.cexp
    have hm := (hfd t).mul he
    exact hm.congr_deriv (by simp only [id, Complex.ofReal_one, mul_one]; ring)
  have hconst : ∀ t : ℝ, f t * Complex.exp (-(c * (t:ℂ))) = 1 := by
    intro t
    have := is_const_of_deriv_eq_zero (fun u => (hg u).differentiableAt) (fun u => (hg u).deriv) t 0
    simpa [h0] using this
  have hexp : ∀ t : ℝ, f t = Complex.exp (c * t) := by
    intro t
    have h3 := hconst t
    calc f t = f t * Complex.exp (-(c * (t:ℂ))) * Complex.exp (c * t) := by
          rw [mul_assoc, ← Complex.exp_add]; simp
      _ = Complex.exp (c * t) := by rw [h3, one_mul]
  have hre : c.re = 0 := by
    have h4 := hnorm 1
    rw [hexp 1, Complex.norm_exp] at h4
    simpa using h4
  refine ⟨c.im, fun t => ?_⟩
  rw [hexp t]
  congr 1
  apply Complex.ext <;> simp [hre]

end Bl.general_b_fact_left_variant
