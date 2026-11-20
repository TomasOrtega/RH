import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf

noncomputable section

open MeasureTheory Filter Topology
open PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG

/- English proof (translation)
Use `show ‖(Complex.exp z + Complex.exp (-z)) / 2‖ ≤ _`. Establish `h1 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖`. Rewrite using `[Complex.norm_exp]`. Conclude with `Real.exp_le_exp.2 (le_trans (le_abs_self _) (Complex.abs_re_le_norm z))`. Establish `h2 : ‖Complex.exp (-z)‖ ≤ Real.exp ‖z‖`.

Rewrite using `[Complex.norm_exp]`. Conclude with `Real.exp_le_exp.2 (by`. Use `Complex.abs_re_le_norm z` as an intermediate fact. Simplify using `only [Complex.neg_re]`. Combine the linear relations using `[neg_abs_le z.re])`.

Rewrite using `[norm_div]`. Establish `h2' : ‖(2 : ℂ)‖ = 2` using `by simp`. Rewrite using `[h2']`. Use `norm_add_le (Complex.exp z) (Complex.exp (-z))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_cosh_le_exp (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp ‖z‖ := by
  show ‖(Complex.exp z + Complex.exp (-z)) / 2‖ ≤ _
  have h1 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (Complex.abs_re_le_norm z))
  have h2 : ‖Complex.exp (-z)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by
      have := Complex.abs_re_le_norm z
      simp only [Complex.neg_re]
      linarith [neg_abs_le z.re])
  rw [norm_div]
  have h2' : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2']
  have := norm_add_le (Complex.exp z) (Complex.exp (-z))
  linarith

/- English proof (translation)
Establish `h` using `Complex.cpow_nat_inv_pow c (n := 2) (by norm_num)`. Rewrite using `[one_div]`. Move the coercions through the operations in `at h`. Conclude with `h`.
-/
theorem sqrt_sq' (c : ℂ) : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
  have h := Complex.cpow_nat_inv_pow c (n := 2) (by norm_num)
  rw [one_div]
  push_cast at h
  exact h

/- English proof (translation)
Establish `h : ‖c ^ (1 / 2 : ℂ)‖ ^ 2 = ‖c‖` using `by rw [← norm_pow, sqrt_sq']`. Use polynomial arithmetic with `[sq_nonneg (‖c ^ (1 / 2 : ℂ)‖ - 1), norm_nonneg (c ^ (1 / 2 : ℂ))]`.
-/
theorem norm_sqrt_le (c : ℂ) : ‖c ^ (1 / 2 : ℂ)‖ ≤ 1 + ‖c‖ := by
  have h : ‖c ^ (1 / 2 : ℂ)‖ ^ 2 = ‖c‖ := by rw [← norm_pow, sqrt_sq']
  nlinarith [sq_nonneg (‖c ^ (1 / 2 : ℂ)‖ - 1), norm_nonneg (c ^ (1 / 2 : ℂ))]

/- English proof (translation)
Rewrite using `[Metric.continuous_iff]`. Introduce `c₀ ε hε`. Establish `hc : Continuous fun w : ℂ => Complex.cosh (t * w)` using `Complex.continuous_cosh.comp (continuous_const.mul continuous_id)`. Take `⟨δ, hδ, hδε⟩` from `Metric.continuous_iff.1 hc (c₀ ^ (1 / 2 : ℂ)) ε hε`. Use `⟨δ ^ 2, by positivity, fun c hcc => ?_⟩` and prove the remaining obligations.

Establish `hprod : (c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)) * (c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)) = c - c₀`. Establish `h1` using `sqrt_sq' c`. Establish `h2` using `sqrt_sq' c₀`. Take the linear combination `h1 - h2`. Establish `hlt : ‖c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ * ‖c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)‖ < δ * δ`.

Rewrite using `[← norm_mul, hprod, ← dist_eq_norm, ← sq]`. Conclude with `hcc`. Distinguish the cases in `h : ‖c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ < δ`. Conclude with `hδε _ (by rwa [dist_eq_norm])`. Establish `h' : ‖-c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ < δ` using `by push Not at h`.

Establish `he : ‖-c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ = ‖c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)‖`. Rewrite using `[← norm_neg]`. Put the polynomial expressions in normal form. Rewrite using `[he]`. Assume the negation of the conclusion as `h2`.

Use `push Not at h2`. Use `mul_le_mul h h2 hδ.le (norm_nonneg _)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `hδε (-c ^ (1 / 2 : ℂ)) (by rwa [dist_eq_norm])` as an intermediate fact. Simplify `this` using `only [mul_neg, Complex.cosh_neg]`.
-/
theorem continuous_cosh_sqrt (t : ℂ) : Continuous fun c : ℂ => Complex.cosh (t * c ^ (1 / 2 : ℂ)) := by
  rw [Metric.continuous_iff]
  intro c₀ ε hε
  have hc : Continuous fun w : ℂ => Complex.cosh (t * w) :=
    Complex.continuous_cosh.comp (continuous_const.mul continuous_id)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 hc (c₀ ^ (1 / 2 : ℂ)) ε hε
  refine ⟨δ ^ 2, by positivity, fun c hcc => ?_⟩
  have hprod : (c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)) * (c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)) = c - c₀ := by
    have h1 := sqrt_sq' c
    have h2 := sqrt_sq' c₀
    linear_combination h1 - h2
  have hlt : ‖c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ * ‖c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)‖ < δ * δ := by
    rw [← norm_mul, hprod, ← dist_eq_norm, ← sq]
    exact hcc
  by_cases h : ‖c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ < δ
  · exact hδε _ (by rwa [dist_eq_norm])
  · have h' : ‖-c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ < δ := by
      push Not at h
      have he : ‖-c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ = ‖c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)‖ := by
        rw [← norm_neg]
        ring_nf
      rw [he]
      by_contra h2
      push Not at h2
      have := mul_le_mul h h2 hδ.le (norm_nonneg _)
      linarith
    have := hδε (-c ^ (1 / 2 : ℂ)) (by rwa [dist_eq_norm])
    simpa only [mul_neg, Complex.cosh_neg] using this

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `c₀`. Establish `hgc : Continuous g` using `hg.1.continuous`. Establish `hF : ∀ c : ℂ, Continuous fun t : ℝ => (g t : ℂ) * Complex.cosh (t * c ^ (1 / 2 : ℂ))` using `fun c => (Complex.continuous_ofReal.comp hgc).mul (Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const))`. Establish `hbc : Continuous fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖))` using `(Complex.continuous_ofReal.comp hgc).norm.mul (Real.continuous_exp.comp (continuous_abs.mul continuous_const))`.

Establish `hbs : HasCompactSupport fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖))`. Use `HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_` and prove the remaining obligations. Establish `hT : T < |t|`. Rewrite `ht` using `[Set.mem_Icc, not_and_or]`. Break down `ht with ht | ht` into its components or cases.

Use `push Not at ht`. Use `neg_abs_le t` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `push Not at ht`. Conclude with `lt_of_lt_of_le ht (le_abs_self t)`.

Simplify using `[hg.2.2 t hT]`. Unfold `coshT`. Use `continuousAt_of_dominated (bound := fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖))) (Eventually.of_forall fun c => (hF c).aestronglyMeasurable) ?_ (hbc.integrable_of_hasCompactSupport hbs) (ae_of_all _ fun t => (continuous_const.mul (continuous_cosh_sqrt (t : ℂ))).continu …` and prove the remaining obligations. Use `filter_upwards [Metric.ball_mem_nhds c₀ one_pos] with c hc`. Use `ae_of_all _ fun t => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Use `(norm_cosh_le_exp _).trans (Real.exp_le_exp.2 ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Use `mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)` and prove the remaining obligations.

Establish `h1` using `norm_sqrt_le c`. Establish `h2 : ‖c‖ ≤ ‖c₀‖ + 1`. Use `norm_le_norm_add_norm_sub' c c₀` as an intermediate fact. Rewrite `hc` using `[Metric.mem_ball, dist_eq_norm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem continuous_coshT {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : Continuous (coshT g) := by
  rw [continuous_iff_continuousAt]
  intro c₀
  have hgc : Continuous g := hg.1.continuous
  have hF : ∀ c : ℂ, Continuous fun t : ℝ => (g t : ℂ) * Complex.cosh (t * c ^ (1 / 2 : ℂ)) := fun c =>
    (Complex.continuous_ofReal.comp hgc).mul
      (Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const))
  have hbc : Continuous fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)) :=
    (Complex.continuous_ofReal.comp hgc).norm.mul
      (Real.continuous_exp.comp (continuous_abs.mul continuous_const))
  have hbs : HasCompactSupport fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_
    have hT : T < |t| := by
      rw [Set.mem_Icc, not_and_or] at ht
      rcases ht with ht | ht
      · push Not at ht
        have := neg_abs_le t
        linarith
      · push Not at ht
        exact lt_of_lt_of_le ht (le_abs_self t)
    simp [hg.2.2 t hT]
  unfold coshT
  refine continuousAt_of_dominated (bound := fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)))
    (Eventually.of_forall fun c => (hF c).aestronglyMeasurable) ?_ (hbc.integrable_of_hasCompactSupport hbs)
    (ae_of_all _ fun t => (continuous_const.mul (continuous_cosh_sqrt (t : ℂ))).continuousAt)
  filter_upwards [Metric.ball_mem_nhds c₀ one_pos] with c hc
  refine ae_of_all _ fun t => ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_cosh_le_exp _).trans (Real.exp_le_exp.2 ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
  have h1 := norm_sqrt_le c
  have h2 : ‖c‖ ≤ ‖c₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' c c₀
    rw [Metric.mem_ball, dist_eq_norm] at hc
    linarith
  linarith

/- English proof (translation)
Introduce `n _ μ M k val T χ χ₀ hk hχ`. Take `⟨m, c, w, g, ks, hg, -, hval⟩` from `hk`. Establish `hv : val = fun χ => ∑ i, c i * zVal (w i) χ * coshT (g i) (cas χ)` using `funext hval`. Rewrite using `[hv]`. Establish `hz : ∀ l : List (Bool × ℕ), Tendsto (fun j => zVal l (χ j)) atTop (𝓝 (zVal l χ₀))`.

Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => simp only [zVal, List.map_nil, List.prod_nil]`. Conclude with `tendsto_const_nhds`. Consider the case `cons p l ih`.

Simplify using `only [zVal, List.map_cons, List.prod_cons] at ih ⊢`. Conclude with `(hχ p.1 p.2).mul ih`. Establish `hcas : Tendsto (fun j => cas (χ j)) atTop (𝓝 (cas χ₀))`. Unfold `cas`. Conclude with `((hχ true 2).add (hχ false 2)).const_mul 2`.

Use `tendsto_finsetSum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `(tendsto_const_nhds.mul (hz (w i))).mul (((continuous_coshT (hg i).1).tendsto _).comp hcas)`.
-/
theorem valCont : ValCont := by
  intro n _ μ M k val T χ χ₀ hk hχ
  obtain ⟨m, c, w, g, ks, hg, -, hval⟩ := hk
  have hv : val = fun χ => ∑ i, c i * zVal (w i) χ * coshT (g i) (cas χ) := funext hval
  rw [hv]
  have hz : ∀ l : List (Bool × ℕ), Tendsto (fun j => zVal l (χ j)) atTop (𝓝 (zVal l χ₀)) := by
    intro l
    induction l with
    | nil => simp only [zVal, List.map_nil, List.prod_nil]; exact tendsto_const_nhds
    | cons p l ih =>
      simp only [zVal, List.map_cons, List.prod_cons] at ih ⊢
      exact (hχ p.1 p.2).mul ih
  have hcas : Tendsto (fun j => cas (χ j)) atTop (𝓝 (cas χ₀)) := by
    unfold cas
    exact ((hχ true 2).add (hχ false 2)).const_mul 2
  refine tendsto_finsetSum _ fun i _ => ?_
  exact (tendsto_const_nhds.mul (hz (w i))).mul (((continuous_coshT (hg i).1).tendsto _).comp hcas)

end PositivityTheory.Rg.BcB.CG

end
