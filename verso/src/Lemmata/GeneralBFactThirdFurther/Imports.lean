import Mathlib

namespace Bl.general_b_fact_third_further

/- English proof (translation)
Establish `h0 : f 0 = 1`. Establish `h` using `hm 0 0`. Simplify using `only [add_zero] at h`. Establish `hne : f 0 ≠ 0`. Introduce `h'`.

Establish `h2` using `hn 0`. Rewrite `h2` using `[h', norm_zero]`. Conclude with `zero_ne_one h2`. Establish `h3 : f 0 * 1 = f 0 * f 0` using `by rw [mul_one]; exact h`. Conclude with `(mul_left_cancel₀ hne h3).symm`.

Use `set F : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, f t with hF`. Establish `hFd : ∀ x, HasDerivAt F (f x) x` using `fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, ne_eq, not_not] at hcon`.

Establish `hF0 : F = fun _ => (0:ℂ)` using `funext hcon`. Establish `h1` using `hFd 0`. Rewrite `h1` using `[hF0]`. Establish `h4` using `h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ))`. Rewrite `h4` using `[h0]`.

Conclude with `one_ne_zero h4`. Establish `key : ∀ s, f s * F δ = F (s + δ) - F s`. Introduce `s`. Simplify using `only [hF]`. Rewrite using `[← intervalIntegral.integral_const_mul]`.

Repeatedly rewrite using `[← hm]`. Rewrite using `[intervalIntegral.integral_comp_add_left (fun t => f t) s, add_zero, intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]`. Use `set a : ℂ := (f δ - 1) / F δ with ha`. Establish `hfd : ∀ s, HasDerivAt f (a * f s) s`. Introduce `s`.

Establish `e : f = fun x => (F (x + δ) - F x) / F δ`. Use function extensionality and compare the values at `fun x => by rw [← key x, mul_div_cancel_right₀ _ hδ]`. Establish `hd : HasDerivAt (fun x => (F (x + δ) - F x) / F δ) ((f (s + δ) - f s) / F δ) s`. Conclude with `(((hFd (s + δ)).comp_add_const s δ).sub (hFd s)).div_const (F δ)`. Rewrite `hd` using `[← e]`.

Use `hd using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hm, ha]`. Clear the denominators using the available nonvanishing facts. Establish `hg : ∀ s, HasDerivAt (fun x : ℝ => f x * Complex.exp (-(a * x))) 0 s`. Introduce `s`.

Establish `h1 : HasDerivAt (fun x : ℝ => a * (x:ℂ)) a s`. Simplify using `using ((hasDerivAt_id (s:ℂ)).const_mul a).comp_ofReal`. Establish `h2` using `(h1.neg).cexp`. Conclude with `((hfd s).mul h2).congr_deriv (by ring)`. Use `⟨a, fun s => ?_⟩` and prove the remaining obligations.

Establish `hcst` using `is_const_of_deriv_eq_zero (f := fun x : ℝ => f x * Complex.exp (-(a * x))) (fun x => (hg x).differentiableAt) (fun x => (hg x).deriv) s 0`. Simplify using `only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, h0] at hcst`. Rewrite `hcst` using `[Complex.exp_neg]`. Conclude with `(mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp hcst`.
-/
private lemma aux (f : ℝ → ℂ) (hc : Continuous f)
    (hm : ∀ s t : ℝ, f (s + t) = f s * f t) (hn : ∀ s, ‖f s‖ = 1) :
    ∃ a : ℂ, ∀ s : ℝ, f s = Complex.exp (a * s) := by
  have h0 : f 0 = 1 := by
    have h := hm 0 0
    simp only [add_zero] at h
    have hne : f 0 ≠ 0 := by
      intro h'
      have h2 := hn 0
      rw [h', norm_zero] at h2
      exact zero_ne_one h2
    have h3 : f 0 * 1 = f 0 * f 0 := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ hne h3).symm
  set F : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, f t with hF
  have hFd : ∀ x, HasDerivAt F (f x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    have hF0 : F = fun _ => (0:ℂ) := funext hcon
    have h1 := hFd 0
    rw [hF0] at h1
    have h4 := h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ))
    rw [h0] at h4
    exact one_ne_zero h4
  have key : ∀ s, f s * F δ = F (s + δ) - F s := by
    intro s
    simp only [hF]
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [← hm]
    rw [intervalIntegral.integral_comp_add_left (fun t => f t) s, add_zero,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  set a : ℂ := (f δ - 1) / F δ with ha
  have hfd : ∀ s, HasDerivAt f (a * f s) s := by
    intro s
    have e : f = fun x => (F (x + δ) - F x) / F δ :=
      funext fun x => by rw [← key x, mul_div_cancel_right₀ _ hδ]
    have hd : HasDerivAt (fun x => (F (x + δ) - F x) / F δ) ((f (s + δ) - f s) / F δ) s := by
      exact (((hFd (s + δ)).comp_add_const s δ).sub (hFd s)).div_const (F δ)
    rw [← e] at hd
    convert hd using 1
    rw [hm, ha]
    field_simp
  have hg : ∀ s, HasDerivAt (fun x : ℝ => f x * Complex.exp (-(a * x))) 0 s := by
    intro s
    have h1 : HasDerivAt (fun x : ℝ => a * (x:ℂ)) a s := by
      simpa using ((hasDerivAt_id (s:ℂ)).const_mul a).comp_ofReal
    have h2 := (h1.neg).cexp
    exact ((hfd s).mul h2).congr_deriv (by ring)
  refine ⟨a, fun s => ?_⟩
  have hcst := is_const_of_deriv_eq_zero (f := fun x : ℝ => f x * Complex.exp (-(a * x)))
    (fun x => (hg x).differentiableAt) (fun x => (hg x).deriv) s 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, h0] at hcst
  rw [Complex.exp_neg] at hcst
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp hcst

/- English proof (translation)
Introduce `f hc hm hn`. Take `⟨a, ha⟩` from `aux f hc hm hn`. Establish `hre : a.re = 0`. Establish `h` using `hn 1`. Rewrite `h` using `[ha, Complex.norm_exp]`.

Simplify using `using h`. Use `⟨a.im, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[ha]`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`.
-/
theorem goal1 :
  ∀ (f : Real → Complex),
  Continuous.{0, 0} f →
    (∀ (s t : Real), Eq.{1} (f (HAdd.hAdd.{0, 0, 0} s t)) (HMul.hMul.{0, 0, 0} (f s) (f t))) →
      (∀ (s : Real), Eq.{1} (Norm.norm.{0} (f s)) 1) →
        Exists.{1} fun (b : Real) ↦
          ∀ (s : Real),
            Eq.{1} (f s) (Complex.exp (HMul.hMul.{0, 0, 0} (Complex.ofReal (HMul.hMul.{0, 0, 0} b s)) Complex.I)) := by
  intro f hc hm hn
  obtain ⟨a, ha⟩ := aux f hc hm hn
  have hre : a.re = 0 := by
    have h := hn 1
    rw [ha, Complex.norm_exp] at h
    simpa using h
  refine ⟨a.im, fun s => ?_⟩
  rw [ha]
  congr 1
  apply Complex.ext <;> simp [hre]

end Bl.general_b_fact_third_further
