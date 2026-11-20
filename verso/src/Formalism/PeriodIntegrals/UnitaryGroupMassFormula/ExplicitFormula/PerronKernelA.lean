import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectInv

namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real

noncomputable def ker (l : ℝ) (s : ℂ) : ℂ := cexp (l * s) / s

/- English proof (translation)
Unfold `ker`. Rewrite using `[norm_div, Complex.norm_exp, Complex.re_ofReal_mul]`.
-/
lemma norm_ker (l : ℝ) (s : ℂ) : ‖ker l s‖ = Real.exp (l * s.re) / ‖s‖ := by
  unfold ker
  rw [norm_div, Complex.norm_exp, Complex.re_ofReal_mul]

/- English proof (translation)
Rewrite using `[intervalIntegral.integral_comp_mul_left Real.exp hl, integral_exp, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma integral_exp_mul (l a b : ℝ) (hl : l ≠ 0) :
    ∫ x in a..b, Real.exp (l * x) = (Real.exp (l * b) - Real.exp (l * a)) / l := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp hl, integral_exp, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hh' : 0 < |h|` using `abs_pos.2 hh`. Establish `hpt : ∀ x : ℝ, ‖ker l ((x : ℂ) + h * I)‖ ≤ Real.exp (l * x) / |h|`. Introduce `x`. Rewrite using `[norm_ker]`. Establish `hre : ((x : ℂ) + h * I).re = x` using `by simp`.

Establish `him : ((x : ℂ) + h * I).im = h` using `by simp`. Rewrite using `[hre]`. Establish `hn : |h| ≤ ‖(x : ℂ) + h * I‖`. Use `Complex.abs_im_le_norm ((x : ℂ) + h * I)` as an intermediate fact. Rewrite `this` using `[him]`. Then use the resulting hypothesis.

Conclude with `div_le_div_of_nonneg_left (Real.exp_pos _).le hh' hn`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[intervalIntegral.integral_div, integral_exp_mul l a b hl]`.
-/
lemma horiz_bound (l a b h : ℝ) (hl : l ≠ 0) (hh : h ≠ 0) (hab : a ≤ b) :
    ‖∫ x : ℝ in a..b, ker l ((x : ℂ) + h * I)‖ ≤
      (Real.exp (l * b) - Real.exp (l * a)) / l / |h| := by
  have hh' : 0 < |h| := abs_pos.2 hh
  have hpt : ∀ x : ℝ, ‖ker l ((x : ℂ) + h * I)‖ ≤ Real.exp (l * x) / |h| := by
    intro x
    rw [norm_ker]
    have hre : ((x : ℂ) + h * I).re = x := by simp
    have him : ((x : ℂ) + h * I).im = h := by simp
    rw [hre]
    have hn : |h| ≤ ‖(x : ℂ) + h * I‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + h * I)
      rwa [him] at this
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hh' hn
  calc ‖∫ x : ℝ in a..b, ker l ((x : ℂ) + h * I)‖ ≤ ∫ x in a..b, Real.exp (l * x) / |h| :=
        intervalIntegral.norm_integral_le_of_norm_le hab
          (Filter.Eventually.of_forall (fun x _ => hpt x))
          (by apply Continuous.intervalIntegrable; fun_prop)
    _ = (Real.exp (l * b) - Real.exp (l * a)) / l / |h| := by
        rw [intervalIntegral.integral_div, integral_exp_mul l a b hl]

/- English proof (translation)
Establish `hpt : ∀ t ∈ Set.uIoc (-T) T, ‖ker l ((x : ℂ) + t * I)‖ ≤ Real.exp (l * x) / |x|`. Introduce `t _`. Rewrite using `[norm_ker]`. Establish `hre : ((x : ℂ) + t * I).re = x` using `by simp`. Rewrite using `[hre]`.

Establish `hn : |x| ≤ ‖(x : ℂ) + t * I‖`. Use `Complex.abs_re_le_norm ((x : ℂ) + t * I)` as an intermediate fact. Rewrite `this` using `[hre]`. Then use the resulting hypothesis. Conclude with `div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.2 hx) hn`. Use `intervalIntegral.norm_integral_le_of_norm_le_const hpt` as an intermediate fact.

Establish `e : |T - -T| = 2 * T`. Rewrite using `[abs_of_nonneg (by linarith)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[e]`. Conclude with `this`.
-/
lemma vert_bound (l x T : ℝ) (hx : x ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t : ℝ in -T..T, ker l ((x : ℂ) + t * I)‖ ≤ Real.exp (l * x) / |x| * (2 * T) := by
  have hpt : ∀ t ∈ Set.uIoc (-T) T, ‖ker l ((x : ℂ) + t * I)‖ ≤ Real.exp (l * x) / |x| := by
    intro t _
    rw [norm_ker]
    have hre : ((x : ℂ) + t * I).re = x := by simp
    rw [hre]
    have hn : |x| ≤ ‖(x : ℂ) + t * I‖ := by
      have := Complex.abs_re_le_norm ((x : ℂ) + t * I)
      rwa [hre] at this
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.2 hx) hn
  have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have e : |T - -T| = 2 * T := by
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [e] at this
  exact this

/- English proof (translation)
Unfold `rectInt`. Conclude with `Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, c⟩ ⟨b, d⟩ H`.
-/
lemma rectInt_eq_zero (f : ℂ → ℂ) (a b c d : ℝ)
    (H : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc c d)) : rectInt f a b c d = 0 := by
  unfold rectInt
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, c⟩ ⟨b, d⟩ H

/- English proof (translation)
Rewrite using `[hxU]`. Establish `h1 : Real.exp (l * x) ≤ 1` using `Real.exp_le_one_iff.2 hlx`. Establish `h2 : Real.exp (l * x) / U * (2 * T) ≤ 1 / U * (2 * T)`. Apply `mul_le_mul_of_nonneg_right _ (by linarith)` to reduce the goal to its premises. Conclude with `div_le_div_of_nonneg_right h1 hU0.le`.

Establish `h3 : 1 / U * (2 * T) ≤ ε`. Rewrite `hUe` using `[div_le_iff₀ hε]`. Rewrite using `[show 1 / U * (2 * T) = 2 * T / U by ring, div_le_iff₀ hU0]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma far_side_small (l x U T ε : ℝ) (hlx : l * x ≤ 0) (hxU : |x| = U) (hT : 0 < T) (hε : 0 < ε)
    (hU0 : 0 < U) (hUe : 2 * T / ε ≤ U) : Real.exp (l * x) / |x| * (2 * T) ≤ ε := by
  rw [hxU]
  have h1 : Real.exp (l * x) ≤ 1 := Real.exp_le_one_iff.2 hlx
  have h2 : Real.exp (l * x) / U * (2 * T) ≤ 1 / U * (2 * T) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact div_le_div_of_nonneg_right h1 hU0.le
  have h3 : 1 / U * (2 * T) ≤ ε := by
    rw [div_le_iff₀ hε] at hUe
    rw [show 1 / U * (2 * T) = 2 * T / U by ring, div_le_iff₀ hU0]
    linarith
  linarith

/- English proof (translation)
Establish `h1 : ‖L‖ = ‖I * L‖` using `by rw [norm_mul, Complex.norm_I, one_mul]`. Rewrite using `[h1, h]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, Complex.norm_I, one_mul]`. Combine the linear relations using `[norm_sub_le B Tp]`.
-/
lemma three_sides {L B Tp R : ℂ} (h : I * L = B - Tp + I * R) : ‖L‖ ≤ ‖B‖ + ‖Tp‖ + ‖R‖ := by
  have h1 : ‖L‖ = ‖I * L‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  rw [h1, h]
  calc ‖B - Tp + I * R‖ ≤ ‖B - Tp‖ + ‖I * R‖ := norm_add_le _ _
    _ ≤ ‖B‖ + ‖Tp‖ + ‖R‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
      linarith [norm_sub_le B Tp]

/- English proof (translation)
Apply `le_of_forall_pos_le_add` to reduce the goal to its premises. Introduce `ε hε`. Use `set U := max (c + 1) (2 * T / ε) with hU`. Establish `hcU : c < U` using `lt_of_lt_of_le (by linarith) (le_max_left _ _)`. Establish `hU0 : 0 < U` using `by linarith`.

Establish `hUe : 2 * T / ε ≤ U` using `le_max_right _ _`. Establish `hdiff : DifferentiableOn ℂ (ker l) (Set.uIcc c U ×ℂ Set.uIcc (-T) T)`. Introduce `z hz`. Establish `hzre : z.re ∈ Set.uIcc c U` using `hz.1`. Rewrite `hzre` using `[Set.uIcc_of_le hcU.le]`.

Establish `hz0 : z ≠ 0`. Introduce `h`. Establish `h1 : c ≤ z.re` using `hzre.1`. Rewrite `h1` using `[h, Complex.zero_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Unfold `ker`. Conclude with `DifferentiableAt.div (by fun_prop) differentiableAt_id hz0`. Establish `hrect` using `rectInt_eq_zero (ker l) c U (-T) T hdiff`. Unfold `rectInt at hrect`.

Rewrite `hrect` using `[smul_eq_mul, smul_eq_mul]`. Establish `hB` using `horiz_bound l c U (-T) hl.ne (by linarith) hcU.le`. Establish `hTp` using `horiz_bound l c U T hl.ne hT.ne' hcU.le`. Rewrite `hB` using `[abs_neg, abs_of_pos hT]`. Rewrite `hTp` using `[abs_of_pos hT]`.

Establish `hR` using `(vert_bound l U T hU0.ne' hT.le).trans (far_side_small l U U T ε (mul_neg_of_neg_of_pos hl hU0).le (abs_of_pos hU0) hT hε hU0 hUe)`. Establish `hL : I * (∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)) = (∫ x : ℝ in c..U, ker l ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in c..U, ker l ((x : ℂ) + T * I)) + I * ∫ t : ℝ in -T..T, ker l ((U : ℂ) + t * I)`. Take the linear combination `-1 * hrect`. Establish `h3` using `three_sides hL`. Establish `hmono : (Real.exp (l * U) - Real.exp (l * c)) / l / T ≤ Real.exp (l * c) / (-l) / T`.

Rewrite using `[show (Real.exp (l * U) - Real.exp (l * c)) / l = (Real.exp (l * c) - Real.exp (l * U)) / (-l) by ring]`. Apply `div_le_div_of_nonneg_right _ hT.le` to reduce the goal to its premises. Apply `div_le_div_of_nonneg_right _ (by linarith)` to reduce the goal to its premises. Combine the linear relations using `[Real.exp_pos (l * U)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma line_bound_neg (l c T : ℝ) (hl : l < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)‖ ≤ 2 * (Real.exp (l * c) / (-l) / T) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  set U := max (c + 1) (2 * T / ε) with hU
  have hcU : c < U := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hU0 : 0 < U := by linarith
  have hUe : 2 * T / ε ≤ U := le_max_right _ _
  have hdiff : DifferentiableOn ℂ (ker l) (Set.uIcc c U ×ℂ Set.uIcc (-T) T) := by
    intro z hz
    have hzre : z.re ∈ Set.uIcc c U := hz.1
    rw [Set.uIcc_of_le hcU.le] at hzre
    have hz0 : z ≠ 0 := by
      intro h
      have h1 : c ≤ z.re := hzre.1
      rw [h, Complex.zero_re] at h1
      linarith
    apply DifferentiableAt.differentiableWithinAt
    unfold ker
    exact DifferentiableAt.div (by fun_prop) differentiableAt_id hz0
  have hrect := rectInt_eq_zero (ker l) c U (-T) T hdiff
  unfold rectInt at hrect
  rw [smul_eq_mul, smul_eq_mul] at hrect
  have hB := horiz_bound l c U (-T) hl.ne (by linarith) hcU.le
  have hTp := horiz_bound l c U T hl.ne hT.ne' hcU.le
  rw [abs_neg, abs_of_pos hT] at hB
  rw [abs_of_pos hT] at hTp
  have hR := (vert_bound l U T hU0.ne' hT.le).trans
    (far_side_small l U U T ε (mul_neg_of_neg_of_pos hl hU0).le (abs_of_pos hU0) hT hε hU0 hUe)
  have hL : I * (∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)) =
      (∫ x : ℝ in c..U, ker l ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in c..U, ker l ((x : ℂ) + T * I))
        + I * ∫ t : ℝ in -T..T, ker l ((U : ℂ) + t * I) := by
    linear_combination -1 * hrect
  have h3 := three_sides hL
  have hmono : (Real.exp (l * U) - Real.exp (l * c)) / l / T ≤ Real.exp (l * c) / (-l) / T := by
    rw [show (Real.exp (l * U) - Real.exp (l * c)) / l = (Real.exp (l * c) - Real.exp (l * U)) / (-l) by ring]
    apply div_le_div_of_nonneg_right _ hT.le
    apply div_le_div_of_nonneg_right _ (by linarith)
    linarith [Real.exp_pos (l * U)]
  linarith

noncomputable def gl (l : ℝ) : ℂ → ℂ := dslope (fun s : ℂ => cexp (l * s)) 0

/- English proof (translation)
Unfold `gl`. Establish `h : DifferentiableOn ℂ (fun s : ℂ => cexp (↑l * s)) Set.univ` using `(by fun_prop : Differentiable ℂ (fun s : ℂ => cexp (↑l * s))).differentiableOn`. Use `(Complex.differentiableOn_dslope (s := Set.univ) (c := 0) Filter.univ_mem).2 h` as an intermediate fact. Conclude with `differentiableOn_univ.1 this`.
-/
lemma gl_differentiable (l : ℝ) : Differentiable ℂ (gl l) := by
  unfold gl
  have h : DifferentiableOn ℂ (fun s : ℂ => cexp (↑l * s)) Set.univ :=
    (by fun_prop : Differentiable ℂ (fun s : ℂ => cexp (↑l * s))).differentiableOn
  have := (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) Filter.univ_mem).2 h
  exact differentiableOn_univ.1 this

/- English proof (translation)
Unfold `gl ker`. Rewrite using `[dslope_of_ne _ hs, slope_def_field]`. Simplify using `only [mul_zero, Complex.exp_zero, sub_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ker_eq (l : ℝ) {s : ℂ} (hs : s ≠ 0) : ker l s = gl l s + 1 / (s - 0) := by
  unfold gl ker
  rw [dslope_of_ne _ hs, slope_def_field]
  simp only [mul_zero, Complex.exp_zero, sub_zero]
  ring

/- English proof (translation)
Establish `hpt : ∀ t, ker l (γ t) = gl l (γ t) + 1 / (γ t - 0)` using `fun t => ker_eq l (h0 t)`. Repeatedly rewrite using `[hpt]`. Apply `intervalIntegral.integral_add` to reduce the goal to its premises. Apply `Continuous.intervalIntegrable` to reduce the goal to its premises. Conclude with `(gl_differentiable l).continuous.comp hγ`.

Apply `Continuous.intervalIntegrable` to reduce the goal to its premises. Conclude with `continuous_const.div (hγ.sub continuous_const) (fun t => by simpa using h0 t)`.
-/
lemma side_split (l : ℝ) (γ : ℝ → ℂ) (hγ : Continuous γ) (h0 : ∀ t, γ t ≠ 0) (p q : ℝ) :
    ∫ t in p..q, ker l (γ t) = (∫ t in p..q, gl l (γ t)) + ∫ t in p..q, 1 / (γ t - 0) := by
  have hpt : ∀ t, ker l (γ t) = gl l (γ t) + 1 / (γ t - 0) := fun t => ker_eq l (h0 t)
  simp_rw [hpt]
  apply intervalIntegral.integral_add
  · apply Continuous.intervalIntegrable
    exact (gl_differentiable l).continuous.comp hγ
  · apply Continuous.intervalIntegrable
    exact continuous_const.div (hγ.sub continuous_const) (fun t => by simpa using h0 t)

/- English proof (translation)
Establish `hbot : ∀ x : ℝ, (x : ℂ) + c * I ≠ 0`. Introduce `x h`. Use `congrArg Complex.im h` as an intermediate fact. Apply the tactic sequence `simp at this <;> linarith`. Establish `htop : ∀ x : ℝ, (x : ℂ) + d * I ≠ 0`.

Introduce `x h`. Use `congrArg Complex.im h` as an intermediate fact. Apply the tactic sequence `simp at this <;> linarith`. Establish `hright : ∀ y : ℝ, (b : ℂ) + y * I ≠ 0`. Introduce `y h`.

Use `congrArg Complex.re h` as an intermediate fact. Apply the tactic sequence `simp at this <;> linarith`. Establish `hleft : ∀ y : ℝ, (a : ℂ) + y * I ≠ 0`. Introduce `y h`. Use `congrArg Complex.re h` as an intermediate fact.

Apply the tactic sequence `simp at this <;> linarith`. Establish `ftc : ∀ (G : ℂ → ℂ) (γ : ℝ → ℂ) (v : ℂ) (p q : ℝ), (∀ t, HasDerivAt γ v t) → Continuous γ → (∀ t, γ t ≠ 0) → (∀ t ∈ Set.uIcc p q, HasDerivAt G (1 / γ t) (γ t)) → ∫ t in p..q, v * (1 / (γ t - 0)) = G (γ q) - G (γ p)`. Introduce `G γ v p q hγd hγc hne hG`. Apply `intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => G (γ t))` to reduce the goal to its premises. Introduce `t ht beta_reduce`.

Use `(hG t ht).comp t (hγd t)` as an intermediate fact. Rewrite using `[sub_zero, mul_comm]`. Conclude with `this`. Apply `Continuous.intervalIntegrable` to reduce the goal to its premises. Conclude with `continuous_const.mul (continuous_const.div (hγc.sub continuous_const) (fun t => by simpa using hne t))`.

Establish `hdx : ∀ (w : ℂ) (t : ℝ), HasDerivAt (fun x : ℝ => (x : ℂ) + w) 1 t` using `fun w t => by`. Simplify using `using ((hasDerivAt_id (t : ℂ)).add_const w).comp_ofReal`. Establish `hdy : ∀ (w : ℂ) (t : ℝ), HasDerivAt (fun y : ℝ => w + (y : ℂ) * I) I t` using `fun w t => by`. Simplify using `using (((hasDerivAt_id (t : ℂ)).mul_const I).const_add w).comp_ofReal`. Establish `B1 : (∫ x in a..b, 1 / (((x : ℂ) + c * I) - 0)) = Complex.log (b + c * I) - Complex.log (a + c * I)`.

Use `ftc Complex.log (fun x : ℝ => (x : ℂ) + c * I) 1 a b (hdx _) (by fun_prop) hbot (fun t _ => by` as an intermediate fact. Rewrite using `[one_div]`. Conclude with `Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hc.ne))))`. Simplify using `only [one_mul] at this`. Conclude with `this`.

Establish `B2 : (∫ x in a..b, 1 / (((x : ℂ) + d * I) - 0)) = Complex.log (b + d * I) - Complex.log (a + d * I)`. Use `ftc Complex.log (fun x : ℝ => (x : ℂ) + d * I) 1 a b (hdx _) (by fun_prop) htop (fun t _ => by` as an intermediate fact. Rewrite using `[one_div]`. Conclude with `Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hd.ne'))))`. Simplify using `only [one_mul] at this`.

Conclude with `this`. Establish `B3 : I * (∫ y in c..d, 1 / (((b : ℂ) + y * I) - 0)) = Complex.log (b + d * I) - Complex.log (b + c * I)`. Rewrite using `[← intervalIntegral.integral_const_mul]`. Conclude with `ftc Complex.log (fun y : ℝ => (b : ℂ) + y * I) I c d (hdy _) (by fun_prop) hright (fun t _ => by`. Rewrite using `[one_div]`.

Conclude with `Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hb))))`. Establish `B4 : I * (∫ y in c..d, 1 / (((a : ℂ) + y * I) - 0)) = Complex.log (-((a : ℂ) + d * I)) - Complex.log (-((a : ℂ) + c * I))`. Rewrite using `[← intervalIntegral.integral_const_mul]`. Conclude with `ftc (fun z => Complex.log (-z)) (fun y : ℝ => (a : ℂ) + y * I) I c d (hdy _) (by fun_prop) hleft (fun t _ => by`. Establish `hm : -((a : ℂ) + t * I) ∈ Complex.slitPlane` using `Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using ha))`.

Use `(Complex.hasDerivAt_log hm).comp ((a : ℂ) + t * I) (hasDerivAt_neg ((a : ℂ) + t * I)) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals (try rfl)`. Apply the tactic sequence `all_goals (rw [one_div, inv_neg]; ring))`. Establish `hz : ∀ z : ℂ, Complex.log z - Complex.log (-z) = ((Complex.arg z : ℂ) - (Complex.arg (-z) : ℂ)) * I`. Introduce `z`.

Simplify using `only [Complex.log, norm_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1` using `hz ((a : ℂ) + d * I)`. Establish `e2` using `hz ((a : ℂ) + c * I)`. Rewrite `e1` using `[Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simpa using hd)]`.

Rewrite `e2` using `[Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hc)]`. Move the coercions through the operations in `at e1 e2`. Establish `hinv : (∫ x in a..b, 1 / (((x : ℂ) + c * I) - 0)) - (∫ x in a..b, 1 / (((x : ℂ) + d * I) - 0)) + I * (∫ y in c..d, 1 / (((b : ℂ) + y * I) - 0)) - I * (∫ y in c..d, 1 / (((a : ℂ) + y * I) - 0)) = 2 * π * I`. Rewrite using `[B1, B2, B3, B4]`. Take the linear combination `e1 - e2`.

Establish `s1` using `side_split l (fun x : ℝ => (x : ℂ) + c * I) (by fun_prop) hbot a b`. Establish `s2` using `side_split l (fun x : ℝ => (x : ℂ) + d * I) (by fun_prop) htop a b`. Establish `s3` using `side_split l (fun y : ℝ => (b : ℂ) + y * I) (by fun_prop) hright c d`. Establish `s4` using `side_split l (fun y : ℝ => (a : ℂ) + y * I) (by fun_prop) hleft c d`. Use `beta_reduce at s1 s2 s3 s4`.

Establish `hg` using `rectInt_eq_zero (gl l) a b c d (gl_differentiable l).differentiableOn`. Unfold `rectInt at hg ⊢`. Simplify using `only [smul_eq_mul] at hg ⊢`. Rewrite using `[s1, s2, s3, s4]`. Take the linear combination `hg + hinv`.
-/
lemma rectInt_ker (l a b c d : ℝ) (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectInt (ker l) a b c d = 2 * π * I := by
  have hbot : ∀ x : ℝ, (x : ℂ) + c * I ≠ 0 := by
    intro x h
    have := congrArg Complex.im h
    simp at this <;> linarith
  have htop : ∀ x : ℝ, (x : ℂ) + d * I ≠ 0 := by
    intro x h
    have := congrArg Complex.im h
    simp at this <;> linarith
  have hright : ∀ y : ℝ, (b : ℂ) + y * I ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this <;> linarith
  have hleft : ∀ y : ℝ, (a : ℂ) + y * I ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this <;> linarith
  have ftc : ∀ (G : ℂ → ℂ) (γ : ℝ → ℂ) (v : ℂ) (p q : ℝ), (∀ t, HasDerivAt γ v t) → Continuous γ →
      (∀ t, γ t ≠ 0) → (∀ t ∈ Set.uIcc p q, HasDerivAt G (1 / γ t) (γ t)) →
      ∫ t in p..q, v * (1 / (γ t - 0)) = G (γ q) - G (γ p) := by
    intro G γ v p q hγd hγc hne hG
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => G (γ t))
    · intro t ht
      beta_reduce
      have := (hG t ht).comp t (hγd t)
      rw [sub_zero, mul_comm]
      exact this
    · apply Continuous.intervalIntegrable
      exact continuous_const.mul (continuous_const.div (hγc.sub continuous_const) (fun t => by simpa using hne t))
  have hdx : ∀ (w : ℂ) (t : ℝ), HasDerivAt (fun x : ℝ => (x : ℂ) + w) 1 t := fun w t => by
    simpa using ((hasDerivAt_id (t : ℂ)).add_const w).comp_ofReal
  have hdy : ∀ (w : ℂ) (t : ℝ), HasDerivAt (fun y : ℝ => w + (y : ℂ) * I) I t := fun w t => by
    simpa using (((hasDerivAt_id (t : ℂ)).mul_const I).const_add w).comp_ofReal
  have B1 : (∫ x in a..b, 1 / (((x : ℂ) + c * I) - 0)) = Complex.log (b + c * I) - Complex.log (a + c * I) := by
    have := ftc Complex.log (fun x : ℝ => (x : ℂ) + c * I) 1 a b (hdx _) (by fun_prop) hbot
      (fun t _ => by
        rw [one_div]
        exact Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hc.ne))))
    simp only [one_mul] at this
    exact this
  have B2 : (∫ x in a..b, 1 / (((x : ℂ) + d * I) - 0)) = Complex.log (b + d * I) - Complex.log (a + d * I) := by
    have := ftc Complex.log (fun x : ℝ => (x : ℂ) + d * I) 1 a b (hdx _) (by fun_prop) htop
      (fun t _ => by
        rw [one_div]
        exact Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hd.ne'))))
    simp only [one_mul] at this
    exact this
  have B3 : I * (∫ y in c..d, 1 / (((b : ℂ) + y * I) - 0)) = Complex.log (b + d * I) - Complex.log (b + c * I) := by
    rw [← intervalIntegral.integral_const_mul]
    exact ftc Complex.log (fun y : ℝ => (b : ℂ) + y * I) I c d (hdy _) (by fun_prop) hright
      (fun t _ => by
        rw [one_div]
        exact Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hb))))
  have B4 : I * (∫ y in c..d, 1 / (((a : ℂ) + y * I) - 0)) =
      Complex.log (-((a : ℂ) + d * I)) - Complex.log (-((a : ℂ) + c * I)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact ftc (fun z => Complex.log (-z)) (fun y : ℝ => (a : ℂ) + y * I) I c d (hdy _) (by fun_prop) hleft
      (fun t _ => by
        have hm : -((a : ℂ) + t * I) ∈ Complex.slitPlane :=
          Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using ha))
        convert (Complex.hasDerivAt_log hm).comp ((a : ℂ) + t * I) (hasDerivAt_neg ((a : ℂ) + t * I)) using 1
        all_goals (try rfl)
        all_goals (rw [one_div, inv_neg]; ring))
  have hz : ∀ z : ℂ, Complex.log z - Complex.log (-z) = ((Complex.arg z : ℂ) - (Complex.arg (-z) : ℂ)) * I := by
    intro z
    simp only [Complex.log, norm_neg]
    ring
  have e1 := hz ((a : ℂ) + d * I)
  have e2 := hz ((a : ℂ) + c * I)
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simpa using hd)] at e1
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hc)] at e2
  push_cast at e1 e2
  have hinv : (∫ x in a..b, 1 / (((x : ℂ) + c * I) - 0)) - (∫ x in a..b, 1 / (((x : ℂ) + d * I) - 0))
      + I * (∫ y in c..d, 1 / (((b : ℂ) + y * I) - 0)) - I * (∫ y in c..d, 1 / (((a : ℂ) + y * I) - 0))
      = 2 * π * I := by
    rw [B1, B2, B3, B4]
    linear_combination e1 - e2
  have s1 := side_split l (fun x : ℝ => (x : ℂ) + c * I) (by fun_prop) hbot a b
  have s2 := side_split l (fun x : ℝ => (x : ℂ) + d * I) (by fun_prop) htop a b
  have s3 := side_split l (fun y : ℝ => (b : ℂ) + y * I) (by fun_prop) hright c d
  have s4 := side_split l (fun y : ℝ => (a : ℂ) + y * I) (by fun_prop) hleft c d
  beta_reduce at s1 s2 s3 s4
  have hg := rectInt_eq_zero (gl l) a b c d (gl_differentiable l).differentiableOn
  unfold rectInt at hg ⊢
  simp only [smul_eq_mul] at hg ⊢
  rw [s1, s2, s3, s4]
  linear_combination hg + hinv

/- English proof (translation)
Apply `le_of_forall_pos_le_add` to reduce the goal to its premises. Introduce `ε hε`. Use `set U := max 1 (2 * T / ε) with hU`. Establish `hU0 : 0 < U` using `lt_of_lt_of_le one_pos (le_max_left _ _)`. Establish `hUe : 2 * T / ε ≤ U` using `le_max_right _ _`.

Establish `hrect` using `rectInt_ker l (-U) c (-T) T (by linarith) hc (by linarith) hT`. Unfold `rectInt at hrect`. Rewrite `hrect` using `[smul_eq_mul, smul_eq_mul]`. Establish `hB` using `horiz_bound l (-U) c (-T) hl.ne' (by linarith) (by linarith)`. Establish `hTp` using `horiz_bound l (-U) c T hl.ne' hT.ne' (by linarith)`.

Rewrite `hB` using `[abs_neg, abs_of_pos hT]`. Rewrite `hTp` using `[abs_of_pos hT]`. Establish `hR` using `(vert_bound l (-U) T (neg_ne_zero.2 hU0.ne') hT.le).trans (far_side_small l (-U) U T ε (by nlinarith) (by rw [abs_neg, abs_of_pos hU0]) hT hε hU0 hUe)`. Establish `hL : I * ((∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)) - 2 * (π : ℂ)) = (∫ x : ℝ in -U..c, ker l ((x : ℂ) + T * I)) - (∫ x : ℝ in -U..c, ker l ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) + I * ∫ t : ℝ in -T..T, ker l (((-U : ℝ) : ℂ) + t * I)`. Take the linear combination `hrect`.

Establish `h3` using `three_sides hL`. Establish `hmono : (Real.exp (l * c) - Real.exp (l * -U)) / l / T ≤ Real.exp (l * c) / l / T`. Apply `div_le_div_of_nonneg_right _ hT.le` to reduce the goal to its premises. Apply `div_le_div_of_nonneg_right _ hl.le` to reduce the goal to its premises. Combine the linear relations using `[Real.exp_pos (l * -U)]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma line_bound_pos (l c T : ℝ) (hl : 0 < l) (hc : 0 < c) (hT : 0 < T) :
    ‖(∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)) - 2 * π‖ ≤ 2 * (Real.exp (l * c) / l / T) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  set U := max 1 (2 * T / ε) with hU
  have hU0 : 0 < U := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hUe : 2 * T / ε ≤ U := le_max_right _ _
  have hrect := rectInt_ker l (-U) c (-T) T (by linarith) hc (by linarith) hT
  unfold rectInt at hrect
  rw [smul_eq_mul, smul_eq_mul] at hrect
  have hB := horiz_bound l (-U) c (-T) hl.ne' (by linarith) (by linarith)
  have hTp := horiz_bound l (-U) c T hl.ne' hT.ne' (by linarith)
  rw [abs_neg, abs_of_pos hT] at hB
  rw [abs_of_pos hT] at hTp
  have hR := (vert_bound l (-U) T (neg_ne_zero.2 hU0.ne') hT.le).trans
    (far_side_small l (-U) U T ε (by nlinarith) (by rw [abs_neg, abs_of_pos hU0]) hT hε hU0 hUe)
  have hL : I * ((∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)) - 2 * (π : ℂ)) =
      (∫ x : ℝ in -U..c, ker l ((x : ℂ) + T * I)) - (∫ x : ℝ in -U..c, ker l ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        + I * ∫ t : ℝ in -T..T, ker l (((-U : ℝ) : ℂ) + t * I) := by
    linear_combination hrect
  have h3 := three_sides hL
  have hmono : (Real.exp (l * c) - Real.exp (l * -U)) / l / T ≤ Real.exp (l * c) / l / T := by
    apply div_le_div_of_nonneg_right _ hT.le
    apply div_le_div_of_nonneg_right _ hl.le
    linarith [Real.exp_pos (l * -U)]
  linarith

end PI.EF.PK
