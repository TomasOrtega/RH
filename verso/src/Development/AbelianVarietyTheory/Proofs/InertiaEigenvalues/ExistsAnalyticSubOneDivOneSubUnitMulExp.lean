import Mathlib

open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `h`. Establish `h1 : χ * Complex.exp (-((L : ℂ) * (t : ℂ))) = 1` using `(sub_eq_zero.mp h).symm`. Establish `h2` using `congrArg norm h1`. Rewrite `h2` using `[norm_mul, hχ, one_mul, Complex.norm_exp, norm_one]`. Establish `h3 : (-((L : ℂ) * (t : ℂ))).re = 0`.

Use `Real.exp_eq_one_iff _ |>.mp h2` as an intermediate fact. Conclude with `this`. Simplify using `at h3`. Break down `h3 with h3 | h3` into its components or cases. Conclude with `hL.ne' h3`.

Conclude with `ht h3`.
-/
theorem one_sub_unit_mul_exp_ne_zero (L : ℝ) (hL : 0 < L) (χ : ℂ) (hχ : ‖χ‖ = 1) (t : ℝ)
    (ht : t ≠ 0) : 1 - χ * Complex.exp (-((L : ℂ) * (t : ℂ))) ≠ 0 := by
  intro h
  have h1 : χ * Complex.exp (-((L : ℂ) * (t : ℂ))) = 1 := (sub_eq_zero.mp h).symm
  have h2 := congrArg norm h1
  rw [norm_mul, hχ, one_mul, Complex.norm_exp, norm_one] at h2
  have h3 : (-((L : ℂ) * (t : ℂ))).re = 0 := by
    have := Real.exp_eq_one_iff _ |>.mp h2
    exact this
  simp at h3
  rcases h3 with h3 | h3
  · exact hL.ne' h3
  · exact ht h3

/- English proof (translation)
Introduce `L hL χ hχ`. Distinguish the cases in `h1 : χ = 1`. Substitute `h1 set f : ℂ → ℂ := fun w => 1 - Complex.exp (-((L : ℂ) * w)) with hf` using the available equality. Establish `hfd : Differentiable ℂ f`. Rewrite using `[hf]`.

Use `fun_prop`. Establish `hkd : Differentiable ℂ (dslope f 0)`. Rewrite using `[← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]`. Conclude with `hfd.differentiableOn`. Establish `hk : ∀ w : ℂ, w ≠ 0 → dslope f 0 w = f w / w`.

Introduce `w hw`. Rewrite using `[dslope_of_ne _ hw, slope_def_field]`. Simplify using `[hf]`. Establish `hk0 : dslope f 0 0 = L`. Rewrite using `[dslope_same]`.

Establish `: HasDerivAt f (0 - Complex.exp (-((L : ℂ) * 0)) * (-((L : ℂ) * 1))) 0` using `(hasDerivAt_const _ _).sub (((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ)).neg.cexp)`. Rewrite using `[this.deriv]`. Simplify using the standard rewrite rules. Use `⟨fun s => (dslope f 0 (s - 1))⁻¹, ?_, ?_, fun h => absurd rfl h⟩` and prove the remaining obligations. Introduce `x _`.

Establish `hd : Differentiable ℂ (fun s : ℂ => dslope f 0 (s - 1))` using `hkd.comp (differentiable_id.sub_const 1)`. Use `(hd.analyticAt _).inv ?_` and prove the remaining obligations. Distinguish the cases in `hx : x = 1`. Substitute `hx show dslope f 0 (((1 : ℝ) : ℂ) - 1) ≠ 0` using the available equality. Rewrite using `[Complex.ofReal_one, sub_self, hk0]`.

Conclude with `hL.ne'` after adjusting the coercions. Establish `hx' : x - 1 ≠ 0` using `sub_ne_zero.mpr hx`. Establish `hx'' : (x : ℂ) - 1 ≠ 0` using `by exact_mod_cast hx'`. Use `show dslope f 0 ((x : ℂ) - 1) ≠ 0`. Rewrite using `[hk _ hx'']`.

Use `div_ne_zero ?_ hx''` and prove the remaining obligations. Use `one_sub_unit_mul_exp_ne_zero L hL 1 hχ (x - 1) hx'` as an intermediate fact. Simplify `this` using `[hf]`. Introduce `x hx`. Establish `hx' : x - 1 ≠ 0` using `sub_ne_zero.mpr hx.ne'`.

Establish `hx'' : (x : ℂ) - 1 ≠ 0` using `by exact_mod_cast hx'`. Use `show (dslope f 0 ((x : ℂ) - 1))⁻¹ = _`. Rewrite using `[hk _ hx'', inv_div, one_mul]`. Use `⟨fun s => (s - 1) / (1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))), ?_, fun _ _ => rfl, fun _ => by simp⟩` and prove the remaining obligations. Introduce `x _`.

Establish `hd : Differentiable ℂ (fun s : ℂ => 1 - χ * Complex.exp (-((L : ℂ) * (s - 1))))` using `by fun_prop`. Establish `hn : Differentiable ℂ (fun s : ℂ => s - 1)` using `by fun_prop`. Use `(hn.analyticAt _).div (hd.analyticAt _) ?_` and prove the remaining obligations. Distinguish the cases in `hx : x = 1`. Substitute `hx` using the available equality.

Simplify `fun h => h1 (Eq.symm h)` using `[sub_eq_zero]`. Use `one_sub_unit_mul_exp_ne_zero L hL χ hχ (x - 1) (sub_ne_zero.mpr hx)` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_analytic_sub_one_div_one_sub_unit_mul_exp :
    ∀ (L : ℝ), 0 < L → ∀ χ : ℂ, ‖χ‖ = 1 → ∃ h : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ h (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → h (x : ℂ) = ((x : ℂ) - 1) / (1 - χ * Complex.exp (-((L : ℂ) * ((x : ℂ) - 1))))) ∧ (χ ≠ 1 → h 1 = 0) := by
  intro L hL χ hχ
  by_cases h1 : χ = 1
  · subst h1
    set f : ℂ → ℂ := fun w => 1 - Complex.exp (-((L : ℂ) * w)) with hf
    have hfd : Differentiable ℂ f := by
      rw [hf]; fun_prop
    have hkd : Differentiable ℂ (dslope f 0) := by
      rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
      exact hfd.differentiableOn
    have hk : ∀ w : ℂ, w ≠ 0 → dslope f 0 w = f w / w := by
      intro w hw
      rw [dslope_of_ne _ hw, slope_def_field]
      simp [hf]
    have hk0 : dslope f 0 0 = L := by
      rw [dslope_same]
      have : HasDerivAt f (0 - Complex.exp (-((L : ℂ) * 0)) * (-((L : ℂ) * 1))) 0 :=
        (hasDerivAt_const _ _).sub (((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ)).neg.cexp)
      rw [this.deriv]; simp
    refine ⟨fun s => (dslope f 0 (s - 1))⁻¹, ?_, ?_, fun h => absurd rfl h⟩
    · intro x _
      have hd : Differentiable ℂ (fun s : ℂ => dslope f 0 (s - 1)) :=
        hkd.comp (differentiable_id.sub_const 1)
      refine (hd.analyticAt _).inv ?_
      by_cases hx : x = 1
      · subst hx
        show dslope f 0 (((1 : ℝ) : ℂ) - 1) ≠ 0
        rw [Complex.ofReal_one, sub_self, hk0]
        exact_mod_cast hL.ne'
      · have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
        have hx'' : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast hx'
        show dslope f 0 ((x : ℂ) - 1) ≠ 0
        rw [hk _ hx'']
        refine div_ne_zero ?_ hx''
        have := one_sub_unit_mul_exp_ne_zero L hL 1 hχ (x - 1) hx'
        simpa [hf] using this
    · intro x hx
      have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx.ne'
      have hx'' : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast hx'
      show (dslope f 0 ((x : ℂ) - 1))⁻¹ = _
      rw [hk _ hx'', inv_div, one_mul]
  · refine ⟨fun s => (s - 1) / (1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))), ?_, fun _ _ => rfl,
      fun _ => by simp⟩
    intro x _
    have hd : Differentiable ℂ (fun s : ℂ => 1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))) := by
      fun_prop
    have hn : Differentiable ℂ (fun s : ℂ => s - 1) := by fun_prop
    refine (hn.analyticAt _).div (hd.analyticAt _) ?_
    by_cases hx : x = 1
    · subst hx
      simpa [sub_eq_zero] using fun h => h1 (Eq.symm h)
    · have := one_sub_unit_mul_exp_ne_zero L hL χ hχ (x - 1) (sub_ne_zero.mpr hx)
      simpa using this

end GlobalTheory
