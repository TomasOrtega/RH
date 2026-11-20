import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TubeSummability

namespace ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion

open Complex MeasureTheory Metric ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.TubeSummability

variable {n : ℕ}

/- English proof (translation)
Establish `hx : ∀ (G Sx Sy : ℂ), G * cexp (-2 * Real.pi * I * Sx) = cexp (-2 * Real.pi * Sy) * (G * cexp (-2 * Real.pi * I * (Sx + Sy * I)))`. Introduce `G Sx Sy`. Rewrite using `[mul_left_comm, ← Complex.exp_add]`. Use `congr 2`. Take the linear combination `(2 * (Real.pi : ℂ) * Sy) * Complex.I_sq`.

Establish `key : ∀ x : Fin n → ℝ, g ((fun j => (x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) + fun j => (y0 j : ℂ) * I) * cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I)) = (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) * (g (fun j => (x j : …`. Introduce `x`. Establish `hg : ((fun j => (x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) + fun j => (y0 j : ℂ) * I) = fun j => (x j : ℂ) + (y0 j : ℂ) * I`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Establish `e1 : ∑ j, (k j : ℂ) * ((x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) = ∑ j, (k j : ℂ) * (x j : ℂ)` using `by simp`. Establish `e2 : ∑ j, (k j : ℂ) * ((x j : ℂ) + (y0 j : ℂ) * I) = ∑ j, (k j : ℂ) * (x j : ℂ) + (∑ j, (k j : ℂ) * (y0 j : ℂ)) * I`. Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `e3 : ((Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℝ) : ℂ) = cexp (-2 * Real.pi * ∑ j, (k j : ℂ) * (y0 j : ℂ))`. Rewrite using `[Complex.ofReal_exp]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hg, e1, e2, e3]`. Conclude with `hx _ _ _`. Unfold `fourCoeff`. Rewrite using `[← MeasureTheory.integral_const_mul]`. Conclude with `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key)`.
-/
lemma fourCoeff_shift (g : (Fin n → ℂ) → ℂ) (y0 : Fin n → ℝ) (k : Fin n → ℤ) :
    fourCoeff (fun t => g (t + fun j => (y0 j : ℂ) * I)) 0 k =
      (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) * fourCoeff g y0 k := by
  have hx : ∀ (G Sx Sy : ℂ), G * cexp (-2 * Real.pi * I * Sx) =
      cexp (-2 * Real.pi * Sy) * (G * cexp (-2 * Real.pi * I * (Sx + Sy * I))) := by
    intro G Sx Sy
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    linear_combination (2 * (Real.pi : ℂ) * Sy) * Complex.I_sq
  have key : ∀ x : Fin n → ℝ,
      g ((fun j => (x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) + fun j => (y0 j : ℂ) * I) *
        cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I)) =
      (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) *
        (g (fun j => (x j : ℂ) + (y0 j : ℂ) * I) *
          cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((x j : ℂ) + (y0 j : ℂ) * I))) := by
    intro x
    have hg : ((fun j => (x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) + fun j => (y0 j : ℂ) * I) =
        fun j => (x j : ℂ) + (y0 j : ℂ) * I := by
      funext j; simp
    have e1 : ∑ j, (k j : ℂ) * ((x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) =
        ∑ j, (k j : ℂ) * (x j : ℂ) := by simp
    have e2 : ∑ j, (k j : ℂ) * ((x j : ℂ) + (y0 j : ℂ) * I) =
        ∑ j, (k j : ℂ) * (x j : ℂ) + (∑ j, (k j : ℂ) * (y0 j : ℂ)) * I := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have e3 : ((Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℝ) : ℂ) =
        cexp (-2 * Real.pi * ∑ j, (k j : ℂ) * (y0 j : ℂ)) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hg, e1, e2, e3]
    exact hx _ _ _
  unfold fourCoeff
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key)

/- English proof (translation)
Break down `lt_trichotomy a 0 with h | rfl | h` into its components or cases. Rewrite using `[Int.sign_eq_neg_one_of_neg h, abs_of_neg (by exact_mod_cast h)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Rewrite using `[Int.sign_eq_one_of_pos h, abs_of_pos (by exact_mod_cast h)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mul_sign_abs (a : ℤ) : (a : ℝ) * (a.sign : ℝ) = |(a : ℝ)| := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg (by exact_mod_cast h)]
    push_cast
    ring
  · simp
  · rw [Int.sign_eq_one_of_pos h, abs_of_pos (by exact_mod_cast h)]
    push_cast
    ring

/- English proof (translation)
Apply the tactic sequence `rcases Int.sign_trichotomy a with h | h | h <;> simp [h]`.
-/
lemma abs_sign_le (a : ℤ) : |(a.sign : ℝ)| ≤ 1 := by
  rcases Int.sign_trichotomy a with h | h | h <;> simp [h]

/- English proof (translation)
Establish `e : (c : ℂ) * I * ∑ j, (k j : ℂ) * (x0 j : ℂ) = ((c * ∑ j, (k j : ℝ) * x0 j : ℝ) : ℂ) * I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.norm_exp_ofReal_mul_I]`.
-/
lemma norm_exp_real_I (c : ℝ) (k : Fin n → ℤ) (x0 : Fin n → ℝ) :
    ‖cexp (c * I * ∑ j, (k j : ℂ) * (x0 j : ℂ))‖ = 1 := by
  have e : (c : ℂ) * I * ∑ j, (k j : ℂ) * (x0 j : ℂ) =
      ((c * ∑ j, (k j : ℝ) * x0 j : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Take `⟨x0, y0, hux, hy0Ω⟩ : ∃ x0 y0 : Fin n → ℝ, (∀ j, u j = (x0 j : ℂ) + (y0 j : ℂ) * I) ∧ y0 ∈ Ω` from `⟨fun j => (u j).re, fun j => (u j).im, fun j => (Complex.re_add_im (u j)).symm, hu⟩`. Establish `hpre : IsPreconnected Ω` using `hc.isPreconnected`. Establish `hind : ∀ b ∈ Ω, ∀ k, fourCoeff h 0 k = fourCoeff h b k` using `fun b hb k => four_indep n Ω h hΩ hpre hd hp 0 h0 b hb k`. Establish `htube : ∀ x b : Fin n → ℝ, b ∈ Ω → (fun j => (x j : ℂ) + (b j : ℂ) * I) ∈ tube n Ω`. Introduce `x b hb`.

Simplify using `only [tube, Set.mem_setOf_eq]`. Simplify using `using hb`. Establish `hslice : ∀ b ∈ Ω, ∃ C, ∀ x : Fin n → ℝ, ‖h (fun j => (x j : ℂ) + (b j : ℂ) * I)‖ ≤ C`. Introduce `b hb`. Establish `hcont : ContinuousOn (fun x : Fin n → ℝ => h (fun j => (x j : ℂ) + (b j : ℂ) * I)) (Set.Icc 0 1)`.

Use `hd.continuousOn.comp (Continuous.continuousOn ?_) (fun x _ => htube x b hb)` and prove the remaining obligations. Conclude with `continuous_pi fun j => (Complex.continuous_ofReal.comp (continuous_apply j)).add continuous_const`. Take `⟨C, hC⟩` from `isCompact_Icc.exists_bound_of_continuousOn hcont`. Use `⟨C, fun x => ?_⟩` and prove the remaining obligations. Establish `hxm : (fun j => x j - (⌊x j⌋ : ℝ)) ∈ Set.Icc (0 : Fin n → ℝ) 1`.

Use `⟨fun j => ?_, fun j => ?_⟩` and prove the remaining obligations. Use `Int.floor_le (x j) show (0 : ℝ) ≤ x j - (⌊x j⌋ : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `Int.lt_floor_add_one (x j) show x j - (⌊x j⌋ : ℝ) ≤ 1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hper` using `hp _ (htube (fun j => x j - (⌊x j⌋ : ℝ)) b hb) (fun j => ⌊x j⌋)`. Establish `heq : ((fun j => (((x j - (⌊x j⌋ : ℝ)) : ℝ) : ℂ) + (b j : ℂ) * I) + fun j => ((⌊x j⌋ : ℤ) : ℂ)) = fun j => (x j : ℂ) + (b j : ℂ) * I`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.add_apply]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hper` using `[heq]`. Rewrite using `[hper]`. Conclude with `hC _ hxm`. Establish `hcoef : ∀ b ∈ Ω, ∃ C, ∀ k : Fin n → ℤ, ‖fourCoeff h 0 k‖ ≤ C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j)`.

Introduce `b hb`. Take `⟨C, hC⟩` from `hslice b hb`. Use `⟨C, fun k => ?_⟩` and prove the remaining obligations. Establish `hB` using `four_bound n h b k C hC`. Rewrite using `[hind b hb k]`.

Establish `hmul : Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * b j) * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) = 1`. Rewrite using `[← Real.exp_add, ← Real.exp_zero]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.

Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp hΩ y0 hy0Ω`. Establish `hbσ : ∀ k : Fin n → ℤ, (fun j => y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) ∈ Ω`. Introduce `k`. Apply `hball` to reduce the goal to its premises. Rewrite using `[Metric.mem_ball, dist_pi_lt_iff hε]`.

Introduce `j`. Rewrite using `[Real.dist_eq, show y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ) - y0 j = -(ε / 2 * (((k j).sign : ℤ) : ℝ)) by ring, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ε / 2)]`. Use `abs_sign_le (k j)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hcoefσ : ∀ σ : Fin n → ℤ, ∃ C, 0 ≤ C ∧ ((fun j => y0 j - ε / 2 * ((σ j : ℤ) : ℝ)) ∈ Ω → ∀ k : Fin n → ℤ, ‖fourCoeff h 0 k‖ ≤ C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * (y0 j - ε / 2 * ((σ j : ℤ) : ℝ))))`.

Introduce `σ`. Distinguish the cases in `hσ : (fun j => y0 j - ε / 2 * ((σ j : ℤ) : ℝ)) ∈ Ω`. Take `⟨C, hC⟩` from `hcoef _ hσ`. Conclude with `⟨max C 0, le_max_right _ _, fun _ k => (hC k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩`. Conclude with `⟨0, le_rfl, fun h' => absurd h' hσ⟩`.

Use `choose Cf hCf0 hCf using hcoefσ`. Establish `hsignS : ∀ k : Fin n → ℤ, (fun j => (k j).sign) ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ))`. Introduce `k`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `j`.

Apply the tactic sequence `rcases Int.sign_trichotomy (k j) with h' | h' | h' <;> simp [h']`. Establish `hCK : ∀ k : Fin n → ℤ, Cf (fun j => (k j).sign) ≤ ∑ σ ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)), Cf σ` using `fun k => Finset.single_le_sum (fun σ _ => hCf0 σ) (hsignS k)`. Establish `hexpo : ∀ k : Fin n → ℤ, 2 * Real.pi * ∑ j, (k j : ℝ) * (y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) + -2 * Real.pi * ∑ j, (k j : ℝ) * y0 j = -(Real.pi * ε) * ∑ j, |(k j : ℝ)|`. Introduce `k`. Establish `e : ∑ j, (k j : ℝ) * (y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) = ∑ j, (k j : ℝ) * y0 j - ε / 2 * ∑ j, |(k j : ℝ)|`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[← mul_sign_abs (k j)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsumu : ∀ k : Fin n → ℤ, ∑ j, (k j : ℂ) * u j = ((∑ j, (k j : ℝ) * x0 j : ℝ) : ℂ) + ((∑ j, (k j : ℝ) * y0 j : ℝ) : ℂ) * I`. Introduce `k`. Simplify using `only [hux]`. Use `push_cast`.

Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hexpu : ∀ A B : ℝ, cexp (2 * Real.pi * I * ((A : ℂ) + (B : ℂ) * I)) = ((Real.exp (-2 * Real.pi * B) : ℝ) : ℂ) * cexp (((2 * Real.pi * A : ℝ) : ℂ) * I)`. Introduce `A B`.

Rewrite using `[Complex.ofReal_exp, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Take the linear combination `(2 * (Real.pi : ℂ) * B) * Complex.I_sq`. Establish `hterm : ∀ k : Fin n → ℤ, ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖ = ‖fourCoeff h 0 k‖ * Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j)`.

Introduce `k`. Rewrite using `[hsumu k, hexpu, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]`. Establish `hbound : ∀ k : Fin n → ℤ, ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖ ≤ (∑ σ ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)), Cf σ) * Real.exp (-(Real.pi * ε) * ∑ j, |(k j : ℝ)|)`. Introduce `k`. Rewrite using `[hterm k]`.

Use `le_trans (mul_le_mul_of_nonneg_right (hCf _ (hbσ k) k) (Real.exp_pos _).le) ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← Real.exp_add]`. Use `mul_le_mul (hCK k) (le_of_eq ?_) (Real.exp_pos _).le (le_trans (hCf0 _) (hCK k))` and prove the remaining obligations. Use `congr 1`. Conclude with `hexpo k`.

Establish `hsumm : Summable (fun k : Fin n → ℤ => ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖)` using `Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound ((summable_exp_abs (Real.pi * ε) (by positivity) n).mul_left _)`. Use `⟨hsumm, ?_⟩` and prove the remaining obligations. Establish `hΩ'o : IsOpen ((fun b => b + y0) ⁻¹' Ω)` using `hΩ.preimage (continuous_id.add continuous_const)`. Establish `h0' : (0 : Fin n → ℝ) ∈ (fun b => b + y0) ⁻¹' Ω` using `by simpa using hy0Ω`. Establish `hmaps : ∀ t ∈ tube n ((fun b => b + y0) ⁻¹' Ω), t + (fun j => (y0 j : ℂ) * I) ∈ tube n Ω`.

Introduce `t ht`. Simplify using `only [tube, Set.mem_setOf_eq, Set.mem_preimage] at ht ⊢`. Use `ht using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Establish `hdg : DifferentiableOn ℂ (fun t => h (t + fun j => (y0 j : ℂ) * I)) (tube n ((fun b => b + y0) ⁻¹' Ω))` using `hd.comp (differentiable_id.add_const _).differentiableOn (fun t ht => hmaps t ht)`. Establish `hpg : ∀ s ∈ tube n ((fun b => b + y0) ⁻¹' Ω), ∀ m : Fin n → ℤ, h (s + (fun k => (m k : ℂ)) + fun j => (y0 j : ℂ) * I) = h (s + fun j => (y0 j : ℂ) * I)`. Introduce `s hs m`. Rewrite using `[add_right_comm]`. Conclude with `hp _ (hmaps s hs) m`.

Establish `hcoefg : ∀ k, fourCoeff (fun t => h (t + fun j => (y0 j : ℂ) * I)) 0 k = (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) * fourCoeff h 0 k`. Introduce `k`. Rewrite using `[fourCoeff_shift h y0 k, hind y0 hy0Ω k]`. Establish `hsummg : Summable (fun k => ‖fourCoeff (fun t => h (t + fun j => (y0 j : ℂ) * I)) 0 k‖)`. Use `hsumm.congr (fun k => ?_)` and prove the remaining obligations.

Rewrite using `[hterm k, hcoefg k, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]`. Establish `hs` using `four_sum n ((fun b => b + y0) ⁻¹' Ω) (fun t => h (t + fun j => (y0 j : ℂ) * I)) hΩ'o hdg hpg h0' hsummg x0`. Use `hs using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Rewrite using `[hcoefg k, hsumu k, hexpu]`.

Establish `e : ((2 * Real.pi * (∑ j, (k j : ℝ) * x0 j) : ℝ) : ℂ) * I = 2 * Real.pi * I * ∑ j, (k j : ℂ) * (x0 j : ℂ)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.

Use `show h u = h ((fun k => (x0 k : ℂ)) + fun j => (y0 j : ℂ) * I)`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[hux j]`. Both sides reduce to the same expression.
-/
theorem tube_expansion (Ω : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (hΩ : IsOpen Ω)
    (hc : Convex ℝ Ω) (h0 : (0 : Fin n → ℝ) ∈ Ω) (hd : DifferentiableOn ℂ h (tube n Ω))
    (hp : ∀ s ∈ tube n Ω, ∀ m : Fin n → ℤ, h (s + fun k => (m k : ℂ)) = h s)
    (u : Fin n → ℂ) (hu : u ∈ tube n Ω) :
    Summable (fun k : Fin n → ℤ =>
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖) ∧
    HasSum (fun k : Fin n → ℤ => fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j))
      (h u) := by
  classical
  obtain ⟨x0, y0, hux, hy0Ω⟩ : ∃ x0 y0 : Fin n → ℝ,
      (∀ j, u j = (x0 j : ℂ) + (y0 j : ℂ) * I) ∧ y0 ∈ Ω :=
    ⟨fun j => (u j).re, fun j => (u j).im, fun j => (Complex.re_add_im (u j)).symm, hu⟩
  have hpre : IsPreconnected Ω := hc.isPreconnected

  have hind : ∀ b ∈ Ω, ∀ k, fourCoeff h 0 k = fourCoeff h b k :=
    fun b hb k => four_indep n Ω h hΩ hpre hd hp 0 h0 b hb k
  have htube : ∀ x b : Fin n → ℝ, b ∈ Ω → (fun j => (x j : ℂ) + (b j : ℂ) * I) ∈ tube n Ω := by
    intro x b hb
    simp only [tube, Set.mem_setOf_eq]
    simpa using hb

  have hslice : ∀ b ∈ Ω, ∃ C, ∀ x : Fin n → ℝ, ‖h (fun j => (x j : ℂ) + (b j : ℂ) * I)‖ ≤ C := by
    intro b hb
    have hcont : ContinuousOn (fun x : Fin n → ℝ => h (fun j => (x j : ℂ) + (b j : ℂ) * I))
        (Set.Icc 0 1) := by
      refine hd.continuousOn.comp (Continuous.continuousOn ?_) (fun x _ => htube x b hb)
      exact continuous_pi fun j => (Complex.continuous_ofReal.comp (continuous_apply j)).add
        continuous_const
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    refine ⟨C, fun x => ?_⟩
    have hxm : (fun j => x j - (⌊x j⌋ : ℝ)) ∈ Set.Icc (0 : Fin n → ℝ) 1 := by
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := Int.floor_le (x j)
        show (0 : ℝ) ≤ x j - (⌊x j⌋ : ℝ)
        linarith
      · have := Int.lt_floor_add_one (x j)
        show x j - (⌊x j⌋ : ℝ) ≤ 1
        linarith
    have hper := hp _ (htube (fun j => x j - (⌊x j⌋ : ℝ)) b hb) (fun j => ⌊x j⌋)
    have heq : ((fun j => (((x j - (⌊x j⌋ : ℝ)) : ℝ) : ℂ) + (b j : ℂ) * I) +
        fun j => ((⌊x j⌋ : ℤ) : ℂ)) = fun j => (x j : ℂ) + (b j : ℂ) * I := by
      funext j
      simp only [Pi.add_apply]
      push_cast
      ring
    rw [heq] at hper
    rw [hper]
    exact hC _ hxm

  have hcoef : ∀ b ∈ Ω, ∃ C, ∀ k : Fin n → ℤ,
      ‖fourCoeff h 0 k‖ ≤ C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) := by
    intro b hb
    obtain ⟨C, hC⟩ := hslice b hb
    refine ⟨C, fun k => ?_⟩
    have hB := four_bound n h b k C hC
    rw [hind b hb k]
    have hmul : Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * b j) *
        Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      congr 1
      ring
    calc ‖fourCoeff h b k‖
        = ‖fourCoeff h b k‖ * Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * b j) *
            Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) := by rw [mul_assoc, hmul, mul_one]
      _ ≤ C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) :=
          mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le

  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ y0 hy0Ω
  have hbσ : ∀ k : Fin n → ℤ, (fun j => y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) ∈ Ω := by
    intro k
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    rw [Real.dist_eq, show y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ) - y0 j =
      -(ε / 2 * (((k j).sign : ℤ) : ℝ)) by ring, abs_neg, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < ε / 2)]
    have := abs_sign_le (k j)
    nlinarith
  have hcoefσ : ∀ σ : Fin n → ℤ, ∃ C, 0 ≤ C ∧
      ((fun j => y0 j - ε / 2 * ((σ j : ℤ) : ℝ)) ∈ Ω → ∀ k : Fin n → ℤ,
        ‖fourCoeff h 0 k‖ ≤
          C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * (y0 j - ε / 2 * ((σ j : ℤ) : ℝ)))) := by
    intro σ
    by_cases hσ : (fun j => y0 j - ε / 2 * ((σ j : ℤ) : ℝ)) ∈ Ω
    · obtain ⟨C, hC⟩ := hcoef _ hσ
      exact ⟨max C 0, le_max_right _ _, fun _ k =>
        (hC k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hσ⟩
  choose Cf hCf0 hCf using hcoefσ
  have hsignS : ∀ k : Fin n → ℤ,
      (fun j => (k j).sign) ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)) := by
    intro k
    rw [Fintype.mem_piFinset]
    intro j
    rcases Int.sign_trichotomy (k j) with h' | h' | h' <;> simp [h']
  have hCK : ∀ k : Fin n → ℤ, Cf (fun j => (k j).sign) ≤
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)), Cf σ :=
    fun k => Finset.single_le_sum (fun σ _ => hCf0 σ) (hsignS k)
  have hexpo : ∀ k : Fin n → ℤ,
      2 * Real.pi * ∑ j, (k j : ℝ) * (y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) +
        -2 * Real.pi * ∑ j, (k j : ℝ) * y0 j = -(Real.pi * ε) * ∑ j, |(k j : ℝ)| := by
    intro k
    have e : ∑ j, (k j : ℝ) * (y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) =
        ∑ j, (k j : ℝ) * y0 j - ε / 2 * ∑ j, |(k j : ℝ)| := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← mul_sign_abs (k j)]
      ring
    rw [e]
    ring

  have hsumu : ∀ k : Fin n → ℤ, ∑ j, (k j : ℂ) * u j =
      ((∑ j, (k j : ℝ) * x0 j : ℝ) : ℂ) + ((∑ j, (k j : ℝ) * y0 j : ℝ) : ℂ) * I := by
    intro k
    simp only [hux]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hexpu : ∀ A B : ℝ, cexp (2 * Real.pi * I * ((A : ℂ) + (B : ℂ) * I)) =
      ((Real.exp (-2 * Real.pi * B) : ℝ) : ℂ) * cexp (((2 * Real.pi * A : ℝ) : ℂ) * I) := by
    intro A B
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * B) * Complex.I_sq
  have hterm : ∀ k : Fin n → ℤ,
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖ =
        ‖fourCoeff h 0 k‖ * Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) := by
    intro k
    rw [hsumu k, hexpu, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hbound : ∀ k : Fin n → ℤ,
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖ ≤
        (∑ σ ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)), Cf σ) *
          Real.exp (-(Real.pi * ε) * ∑ j, |(k j : ℝ)|) := by
    intro k
    rw [hterm k]
    refine le_trans (mul_le_mul_of_nonneg_right (hCf _ (hbσ k) k) (Real.exp_pos _).le) ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul (hCK k) (le_of_eq ?_) (Real.exp_pos _).le (le_trans (hCf0 _) (hCK k))
    congr 1
    exact hexpo k
  have hsumm : Summable (fun k : Fin n → ℤ =>
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound
      ((summable_exp_abs (Real.pi * ε) (by positivity) n).mul_left _)
  refine ⟨hsumm, ?_⟩

  have hΩ'o : IsOpen ((fun b => b + y0) ⁻¹' Ω) := hΩ.preimage (continuous_id.add continuous_const)
  have h0' : (0 : Fin n → ℝ) ∈ (fun b => b + y0) ⁻¹' Ω := by simpa using hy0Ω
  have hmaps : ∀ t ∈ tube n ((fun b => b + y0) ⁻¹' Ω),
      t + (fun j => (y0 j : ℂ) * I) ∈ tube n Ω := by
    intro t ht
    simp only [tube, Set.mem_setOf_eq, Set.mem_preimage] at ht ⊢
    convert ht using 1
    funext j
    simp
  have hdg : DifferentiableOn ℂ (fun t => h (t + fun j => (y0 j : ℂ) * I))
      (tube n ((fun b => b + y0) ⁻¹' Ω)) :=
    hd.comp (differentiable_id.add_const _).differentiableOn (fun t ht => hmaps t ht)
  have hpg : ∀ s ∈ tube n ((fun b => b + y0) ⁻¹' Ω), ∀ m : Fin n → ℤ,
      h (s + (fun k => (m k : ℂ)) + fun j => (y0 j : ℂ) * I) = h (s + fun j => (y0 j : ℂ) * I) := by
    intro s hs m
    rw [add_right_comm]
    exact hp _ (hmaps s hs) m
  have hcoefg : ∀ k, fourCoeff (fun t => h (t + fun j => (y0 j : ℂ) * I)) 0 k =
      (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) * fourCoeff h 0 k := by
    intro k
    rw [fourCoeff_shift h y0 k, hind y0 hy0Ω k]
  have hsummg : Summable (fun k => ‖fourCoeff (fun t => h (t + fun j => (y0 j : ℂ) * I)) 0 k‖) := by
    refine hsumm.congr (fun k => ?_)
    rw [hterm k, hcoefg k, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      mul_comm]
  have hs := four_sum n ((fun b => b + y0) ⁻¹' Ω) (fun t => h (t + fun j => (y0 j : ℂ) * I))
    hΩ'o hdg hpg h0' hsummg x0
  convert hs using 1
  · funext k
    rw [hcoefg k, hsumu k, hexpu]
    have e : ((2 * Real.pi * (∑ j, (k j : ℝ) * x0 j) : ℝ) : ℂ) * I =
        2 * Real.pi * I * ∑ j, (k j : ℂ) * (x0 j : ℂ) := by
      push_cast
      ring
    rw [e]
    ring
  · show h u = h ((fun k => (x0 k : ℂ)) + fun j => (y0 j : ℂ) * I)
    congr 1
    funext j
    rw [hux j]
    rfl

end ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
