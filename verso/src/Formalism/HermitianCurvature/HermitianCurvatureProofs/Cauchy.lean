import Formalism.HermitianCurvature.StatementE

namespace Formalism.FourierDecayAlt.P.Cauchy

open Complex Metric Set

/- English proof (translation)
Proceed by induction on `p with`. Consider the case `zero => simpa using ⟨hF, hfF⟩`. Consider the case `succ p ih`. Take `⟨hd, he⟩` from `ih`. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[iteratedDeriv_succ]`. Conclude with `hd.deriv hU`. Rewrite using `[iteratedDeriv_succ, iteratedDeriv_succ]`. Establish `h0 : HasDerivAt (iteratedDeriv p F) (deriv (iteratedDeriv p F) x) (x : ℂ)` using `(hd.differentiableAt (hU.mem_nhds (hmem x))).hasDerivAt`. Establish `h1 : HasDerivAt (fun y : ℝ => (iteratedDeriv p F y).re) (deriv (iteratedDeriv p F) x).re x` using `h0.real_of_complex`.

Establish `h2 : (fun y : ℝ => (iteratedDeriv p F y).re) = iteratedDeriv p f`. Use function extensionality and compare the values at `y`. Rewrite using `[he y]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2]`.

Establish `h3 : HasDerivAt (fun y : ℝ => iteratedDeriv p F y) (deriv (iteratedDeriv p F) x) x` using `h0.comp_ofReal`. Establish `h4 : (fun y : ℝ => iteratedDeriv p F y) = fun y : ℝ => ((iteratedDeriv p f y : ℝ) : ℂ)`. Use function extensionality and compare the values at `y`. Rewrite using `[he y]`. Rewrite `h3` using `[h4]`.

Establish `h5` using `h3.unique h1.ofReal_comp`. Rewrite using `[h1.deriv]`. Conclude with `h5`.
-/
theorem iteratedDeriv_ofReal {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {f : ℝ → ℝ} (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) (hfF : ∀ x : ℝ, F x = f x) (p : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv p F) U ∧
      ∀ x : ℝ, iteratedDeriv p F x = (iteratedDeriv p f x : ℝ) := by
  induction p with
  | zero => simpa using ⟨hF, hfF⟩
  | succ p ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨?_, fun x => ?_⟩
    · rw [iteratedDeriv_succ]
      exact hd.deriv hU
    · rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have h0 : HasDerivAt (iteratedDeriv p F) (deriv (iteratedDeriv p F) x) (x : ℂ) :=
        (hd.differentiableAt (hU.mem_nhds (hmem x))).hasDerivAt
      have h1 : HasDerivAt (fun y : ℝ => (iteratedDeriv p F y).re)
          (deriv (iteratedDeriv p F) x).re x := h0.real_of_complex
      have h2 : (fun y : ℝ => (iteratedDeriv p F y).re) = iteratedDeriv p f := by
        funext y; rw [he y]; simp
      rw [h2] at h1
      have h3 : HasDerivAt (fun y : ℝ => iteratedDeriv p F y)
          (deriv (iteratedDeriv p F) x) x := h0.comp_ofReal
      have h4 : (fun y : ℝ => iteratedDeriv p F y) = fun y : ℝ => ((iteratedDeriv p f y : ℝ) : ℂ) := by
        funext y; rw [he y]
      rw [h4] at h3
      have h5 := h3.unique h1.ofReal_comp
      rw [h1.deriv]
      exact h5

/- English proof (translation)
Establish `hσ0 : 0 < σ` using `by linarith`. Establish `hx : 0 < 1 - 2 * (1 / (4 * σ))`. Establish `: 1 / (4 * σ) ≤ 1 / 16`. Apply the tactic sequence `apply one_div_le_one_div_of_le <;> linarith`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Real.rpow_def_of_pos hx]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `h1` using `Real.one_sub_inv_le_log_of_pos hx`. Establish `h2 : (1 - 2 * (1 / (4 * σ)))⁻¹ = 2 * σ / (2 * σ - 1)`. Establish `h21 : 1 - 2 * (1 / (4 * σ)) = (2 * σ - 1) / (2 * σ)`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h21, inv_div]`. Rewrite `h1` using `[h2]`. Establish `h3 : 1 - 2 * σ / (2 * σ - 1) = -(1 / (2 * σ - 1))`.

Establish `: 2 * σ - 1 ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h3]`. Establish `h4 : 1 / (2 * σ - 1) ≤ 1 / σ`.

Apply the tactic sequence `apply one_div_le_one_div_of_le <;> linarith`. Establish `h5 : -(1 / σ) ≤ Real.log (1 - 2 * (1 / (4 * σ)))` using `by linarith`. Establish `h6 : σ * -(1 / σ) ≤ σ * Real.log (1 - 2 * (1 / (4 * σ)))` using `mul_le_mul_of_nonneg_left h5 hσ0.le`. Establish `h7 : σ * -(1 / σ) = -1` using `by field_simp`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem rpow_le_exp_one {σ : ℝ} (hσ : 4 ≤ σ) : (1 - 2 * (1 / (4 * σ))) ^ (-σ) ≤ Real.exp 1 := by
  have hσ0 : 0 < σ := by linarith
  have hx : 0 < 1 - 2 * (1 / (4 * σ)) := by
    have : 1 / (4 * σ) ≤ 1 / 16 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  have h1 := Real.one_sub_inv_le_log_of_pos hx
  have h2 : (1 - 2 * (1 / (4 * σ)))⁻¹ = 2 * σ / (2 * σ - 1) := by
    have h21 : 1 - 2 * (1 / (4 * σ)) = (2 * σ - 1) / (2 * σ) := by
      field_simp
      ring
    rw [h21, inv_div]
  rw [h2] at h1
  have h3 : 1 - 2 * σ / (2 * σ - 1) = -(1 / (2 * σ - 1)) := by
    have : 2 * σ - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h3] at h1
  have h4 : 1 / (2 * σ - 1) ≤ 1 / σ := by
    apply one_div_le_one_div_of_le <;> linarith
  have h5 : -(1 / σ) ≤ Real.log (1 - 2 * (1 / (4 * σ))) := by linarith
  have h6 : σ * -(1 / σ) ≤ σ * Real.log (1 - 2 * (1 / (4 * σ))) :=
    mul_le_mul_of_nonneg_left h5 hσ0.le
  have h7 : σ * -(1 / σ) = -1 := by field_simp
  nlinarith

/- English proof (translation)
Use `set a : ℝ := ε * Real.exp (-u) with ha`. Establish `ha0 : 0 < a` using `by positivity`. Establish `h1 : 1 + (ε : ℂ) * Complex.exp (-w) = ((1 + a : ℝ) : ℂ) + (a : ℂ) * (Complex.exp (-(w - u)) - 1)`. Establish `: Complex.exp (-w) = Complex.exp (-(u : ℂ)) * Complex.exp (-(w - u))`. Rewrite using `[← Complex.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, ha]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : ‖Complex.exp (-(w - u)) - 1‖ ≤ 2 * ρ`. Establish `h` using `Complex.norm_exp_sub_one_le (x := -(w - u)) (by rw [norm_neg]; linarith)`. Rewrite `h` using `[norm_neg]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : -(2 * ρ) ≤ (Complex.exp (-(w - u)) - 1).re`.

Use `Complex.abs_re_le_norm (Complex.exp (-(w - u)) - 1)` as an intermediate fact. Use `neg_abs_le (Complex.exp (-(w - u)) - 1).re` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hρ0 : 0 ≤ ρ` using `(norm_nonneg _).trans hw`. Establish `h4 : a * -(2 * ρ) ≤ a * (Complex.exp (-(w - u)) - 1).re` using `mul_le_mul_of_nonneg_left h3 ha0.le`.

Rewrite using `[h1, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem base_bound {ε : ℝ} (hε : 0 < ε) (u : ℝ) {ρ : ℝ} (hρ : ρ ≤ 1 / 16) {w : ℂ}
    (hw : ‖w - u‖ ≤ ρ) :
    (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ (1 + (ε : ℂ) * Complex.exp (-w)).re := by
  set a : ℝ := ε * Real.exp (-u) with ha
  have ha0 : 0 < a := by positivity
  have h1 : 1 + (ε : ℂ) * Complex.exp (-w) = ((1 + a : ℝ) : ℂ) + (a : ℂ) * (Complex.exp (-(w - u)) - 1) := by
    have : Complex.exp (-w) = Complex.exp (-(u : ℂ)) * Complex.exp (-(w - u)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this, ha]
    push_cast
    ring
  have h2 : ‖Complex.exp (-(w - u)) - 1‖ ≤ 2 * ρ := by
    have h := Complex.norm_exp_sub_one_le (x := -(w - u)) (by rw [norm_neg]; linarith)
    rw [norm_neg] at h
    linarith
  have h3 : -(2 * ρ) ≤ (Complex.exp (-(w - u)) - 1).re := by
    have := Complex.abs_re_le_norm (Complex.exp (-(w - u)) - 1)
    have := neg_abs_le (Complex.exp (-(w - u)) - 1).re
    linarith
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hw
  have h4 : a * -(2 * ρ) ≤ a * (Complex.exp (-(w - u)) - 1).re :=
    mul_le_mul_of_nonneg_left h3 ha0.le
  rw [h1, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  nlinarith

end Formalism.FourierDecayAlt.P.Cauchy

namespace Formalism.FourierDecayAlt.P

open Complex Metric Set Formalism.FourierDecayAlt.P.Cauchy

/- English proof (translation)
Introduce `σ ε hσ hε p u`. Establish `hσ0 : 0 < σ` using `by linarith`. Use `set ρ : ℝ := 1 / (4 * σ) with hρdef`. Establish `hρ0 : 0 < ρ` using `by positivity`. Establish `hρ : ρ ≤ 1 / 16`.

Apply the tactic sequence `apply one_div_le_one_div_of_le <;> linarith`. Use `set F : ℂ → ℂ := fun w => (1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ) with hF`. Use `set f : ℝ → ℝ := fun v => (1 + ε * Real.exp (-v)) ^ (-σ) with hf`. Use `set U : Set ℂ := {w | 0 < (1 + (ε : ℂ) * Complex.exp (-w)).re} with hUdef`. Establish `hU : IsOpen U`.

Apply `isOpen_lt continuous_const` to reduce the goal to its premises. Use `fun_prop`. Establish `hFd : DifferentiableOn ℂ F U`. Introduce `w hw`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises.

Apply `DifferentiableAt.cpow_const (by fun_prop)` to reduce the goal to its premises. Conclude with `Or.inl hw`. Establish `hpos : ∀ x : ℝ, 0 < 1 + ε * Real.exp (-x)` using `fun x => by positivity`. Establish `hcast : ∀ x : ℝ, 1 + (ε : ℂ) * Complex.exp (-(x : ℂ)) = ((1 + ε * Real.exp (-x) : ℝ) : ℂ)`. Introduce `x`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : ∀ x : ℝ, (x : ℂ) ∈ U`. Introduce `x`. Use `show 0 < (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))).re`.

Rewrite using `[hcast, Complex.ofReal_re]`. Conclude with `hpos x`. Establish `hfF : ∀ x : ℝ, F x = f x`. Introduce `x`. Use `show (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))) ^ ((-σ : ℝ) : ℂ) = _`.

Rewrite using `[hcast, ← Complex.ofReal_cpow (hpos x).le]`. Establish `key` using `(iteratedDeriv_ofReal hU hFd hmem hfF p).2 u`. Establish `hA : 0 < 1 + ε * Real.exp (-u)` using `hpos u`. Establish `h12 : 0 < 1 - 2 * ρ` using `by linarith`. Establish `hsub : closedBall (u : ℂ) ρ ⊆ U`.

Introduce `w hw`. Use `base_bound hε u hρ (w := w) (by simpa [dist_eq_norm] using hw)` as an intermediate fact. Establish `h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ)` using `by positivity`. Conclude with `lt_of_lt_of_le h0 this`. Establish `hC : ∀ w ∈ sphere (u : ℂ) ρ, ‖F w‖ ≤ Real.exp 1 * (1 + ε * Real.exp (-u)) ^ (-σ)`.

Introduce `w hw`. Establish `hb` using `base_bound hε u hρ (w := w) (by`. Establish `: ‖w - u‖ = ρ` using `by simpa [dist_eq_norm] using hw`. Conclude with `this.le)`. Establish `h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ)` using `by positivity`.

Establish `hn : (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ ‖1 + (ε : ℂ) * Complex.exp (-w)‖` using `hb.trans (Complex.re_le_norm _)`. Use `show ‖(1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ)‖ ≤ _`. Rewrite using `[Complex.norm_cpow_real]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcau` using `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le p hρ0 (hFd.diffContOnCl_ball hsub) hC`.

Rewrite `hcau` using `[key, Complex.norm_real, Real.norm_eq_abs]`. Use `hcau.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hρdef, one_div, inv_pow, div_inv_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cauchy_theta_identity : Formalism.FourierDecayAlt.E.CauchyTheta := by
  intro σ ε hσ hε p u
  have hσ0 : 0 < σ := by linarith
  set ρ : ℝ := 1 / (4 * σ) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ : ρ ≤ 1 / 16 := by
    apply one_div_le_one_div_of_le <;> linarith
  set F : ℂ → ℂ := fun w => (1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ) with hF
  set f : ℝ → ℝ := fun v => (1 + ε * Real.exp (-v)) ^ (-σ) with hf
  set U : Set ℂ := {w | 0 < (1 + (ε : ℂ) * Complex.exp (-w)).re} with hUdef
  have hU : IsOpen U := by
    apply isOpen_lt continuous_const
    fun_prop
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.cpow_const (by fun_prop)
    exact Or.inl hw
  have hpos : ∀ x : ℝ, 0 < 1 + ε * Real.exp (-x) := fun x => by positivity
  have hcast : ∀ x : ℝ, 1 + (ε : ℂ) * Complex.exp (-(x : ℂ)) = ((1 + ε * Real.exp (-x) : ℝ) : ℂ) := by
    intro x; push_cast; ring
  have hmem : ∀ x : ℝ, (x : ℂ) ∈ U := by
    intro x
    show 0 < (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))).re
    rw [hcast, Complex.ofReal_re]
    exact hpos x
  have hfF : ∀ x : ℝ, F x = f x := by
    intro x
    show (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))) ^ ((-σ : ℝ) : ℂ) = _
    rw [hcast, ← Complex.ofReal_cpow (hpos x).le]
  have key := (iteratedDeriv_ofReal hU hFd hmem hfF p).2 u
  have hA : 0 < 1 + ε * Real.exp (-u) := hpos u
  have h12 : 0 < 1 - 2 * ρ := by linarith
  have hsub : closedBall (u : ℂ) ρ ⊆ U := by
    intro w hw
    have := base_bound hε u hρ (w := w) (by simpa [dist_eq_norm] using hw)
    have h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) := by positivity
    exact lt_of_lt_of_le h0 this
  have hC : ∀ w ∈ sphere (u : ℂ) ρ, ‖F w‖ ≤ Real.exp 1 * (1 + ε * Real.exp (-u)) ^ (-σ) := by
    intro w hw
    have hb := base_bound hε u hρ (w := w) (by
      have : ‖w - u‖ = ρ := by simpa [dist_eq_norm] using hw
      exact this.le)
    have h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) := by positivity
    have hn : (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ ‖1 + (ε : ℂ) * Complex.exp (-w)‖ :=
      hb.trans (Complex.re_le_norm _)
    show ‖(1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_cpow_real]
    calc ‖1 + (ε : ℂ) * Complex.exp (-w)‖ ^ (-σ)
        ≤ ((1 + ε * Real.exp (-u)) * (1 - 2 * ρ)) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos h0 hn (by linarith)
      _ = (1 + ε * Real.exp (-u)) ^ (-σ) * (1 - 2 * ρ) ^ (-σ) :=
          Real.mul_rpow hA.le h12.le
      _ ≤ (1 + ε * Real.exp (-u)) ^ (-σ) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (rpow_le_exp_one hσ) (by positivity)
      _ = _ := mul_comm _ _
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le p hρ0
    (hFd.diffContOnCl_ball hsub) hC
  rw [key, Complex.norm_real, Real.norm_eq_abs] at hcau
  refine hcau.trans (le_of_eq ?_)
  rw [hρdef, one_div, inv_pow, div_inv_eq_mul]
  ring

end Formalism.FourierDecayAlt.P
