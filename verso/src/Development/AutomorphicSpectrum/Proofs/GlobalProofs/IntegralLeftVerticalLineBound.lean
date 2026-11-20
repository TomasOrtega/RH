import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.ExplZeta.LeftShift

/- English proof (translation)
Establish `h1 : x ^ σ ≤ (2 : ℝ) ^ σ` using `Real.rpow_le_rpow_of_nonpos (by norm_num) hx hσ`. Establish `h2 : (2 : ℝ) ^ σ = Real.exp (Real.log 2 * σ)` using `Real.rpow_def_of_pos (by norm_num) σ`. Establish `h3 : Real.log 2 * σ ≤ σ / 2`. Use `Real.log_two_gt_d9` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma rpow_le_exp_half {x σ : ℝ} (hx : 2 ≤ x) (hσ : σ ≤ 0) :
    x ^ σ ≤ Real.exp (σ / 2) := by
  have h1 : x ^ σ ≤ (2 : ℝ) ^ σ := Real.rpow_le_rpow_of_nonpos (by norm_num) hx hσ
  have h2 : (2 : ℝ) ^ σ = Real.exp (Real.log 2 * σ) := Real.rpow_def_of_pos (by norm_num) σ
  have h3 : Real.log 2 * σ ≤ σ / 2 := by
    have := Real.log_two_gt_d9
    nlinarith
  calc x ^ σ ≤ (2 : ℝ) ^ σ := h1
    _ = Real.exp (Real.log 2 * σ) := h2
    _ ≤ Real.exp (σ / 2) := Real.exp_le_exp.mpr h3

/- English proof (translation)
Rewrite using `[abs_of_nonpos hσ]`. Establish `h1 : -σ / 4 + 1 ≤ Real.exp (-σ / 4)` using `Real.add_one_le_exp _`. Establish `h2 : Real.exp (σ / 2) = Real.exp (σ / 4) * Real.exp (σ / 4)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : Real.exp (-σ / 4) * Real.exp (σ / 4) = 1`. Rewrite using `[← Real.exp_add]; simp [show -σ / 4 + σ / 4 = 0 by ring]`. Establish `hp` using `Real.exp_pos (σ / 4)`. Establish `h4 : (2 + -σ) * Real.exp (σ / 4) ≤ 4`.

Establish `: (2 + -σ) * Real.exp (σ / 4) ≤ 4 * Real.exp (-σ / 4) * Real.exp (σ / 4)`. Apply `mul_le_mul_of_nonneg_right _ hp.le` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma poly_mul_exp_le {σ : ℝ} (hσ : σ ≤ 0) :
    (2 + |σ|) * Real.exp (σ / 2) ≤ 4 * Real.exp (σ / 4) := by
  rw [abs_of_nonpos hσ]
  have h1 : -σ / 4 + 1 ≤ Real.exp (-σ / 4) := Real.add_one_le_exp _
  have h2 : Real.exp (σ / 2) = Real.exp (σ / 4) * Real.exp (σ / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-σ / 4) * Real.exp (σ / 4) = 1 := by
    rw [← Real.exp_add]; simp [show -σ / 4 + σ / 4 = 0 by ring]
  have hp := Real.exp_pos (σ / 4)
  have h4 : (2 + -σ) * Real.exp (σ / 4) ≤ 4 := by
    have : (2 + -σ) * Real.exp (σ / 4) ≤ 4 * Real.exp (-σ / 4) * Real.exp (σ / 4) := by
      apply mul_le_mul_of_nonneg_right _ hp.le
      linarith
    calc _ ≤ _ := this
      _ = 4 * (Real.exp (-σ / 4) * Real.exp (σ / 4)) := by ring
      _ = 4 := by rw [h3]; ring
  rw [h2]
  calc (2 + -σ) * (Real.exp (σ / 4) * Real.exp (σ / 4))
      = ((2 + -σ) * Real.exp (σ / 4)) * Real.exp (σ / 4) := by ring
    _ ≤ 4 * Real.exp (σ / 4) := mul_le_mul_of_nonneg_right h4 hp.le

/- English proof (translation)
Rewrite using `[norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]`.
-/
lemma norm_quot {g s : ℂ} {x : ℝ} (hx : 2 ≤ x) :
    ‖g * (x : ℂ) ^ s / s‖ = ‖g‖ * x ^ s.re / ‖s‖ := by
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]

/- English proof (translation)
Rewrite using `[norm_quot hx]`. Establish `hn : |s.im| ≤ ‖s‖` using `Complex.abs_im_le_norm s`. Establish `hnpos : 0 < ‖s‖` using `by linarith`. Establish `hxp : 0 ≤ x ^ s.re` using `Real.rpow_nonneg (by linarith) _`. Establish `h1 : ‖g‖ ≤ A * (2 + |s.re|) * ‖s‖`.

Use `hg.trans ?_` and prove the remaining obligations. Establish `h0` using `abs_nonneg s.re`. Establish `: 1 + |s.re| + |s.im| ≤ (2 + |s.re|) * ‖s‖` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_iff₀ hnpos]`.

Establish `h2` using `rpow_le_exp_half hx hs`. Establish `h3` using `poly_mul_exp_le hs`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ hnpos.le` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left h3 hA`.

Use `_ = _ := by ring`.
-/
lemma horiz_bound {g s : ℂ} {A x : ℝ} (hA : 0 ≤ A) (hx : 2 ≤ x) (hs : s.re ≤ 0)
    (him : 1 ≤ |s.im|) (hg : ‖g‖ ≤ A * (1 + |s.re| + |s.im|)) :
    ‖g * (x : ℂ) ^ s / s‖ ≤ 4 * A * Real.exp (s.re / 4) := by
  rw [norm_quot hx]
  have hn : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hnpos : 0 < ‖s‖ := by linarith
  have hxp : 0 ≤ x ^ s.re := Real.rpow_nonneg (by linarith) _
  have h1 : ‖g‖ ≤ A * (2 + |s.re|) * ‖s‖ := by
    refine hg.trans ?_
    have h0 := abs_nonneg s.re
    have : 1 + |s.re| + |s.im| ≤ (2 + |s.re|) * ‖s‖ := by nlinarith
    calc A * (1 + |s.re| + |s.im|) ≤ A * ((2 + |s.re|) * ‖s‖) :=
          mul_le_mul_of_nonneg_left this hA
      _ = _ := by ring
  rw [div_le_iff₀ hnpos]
  have h2 := rpow_le_exp_half hx hs
  have h3 := poly_mul_exp_le hs
  calc ‖g‖ * x ^ s.re ≤ (A * (2 + |s.re|) * ‖s‖) * Real.exp (s.re / 2) :=
        mul_le_mul h1 h2 hxp (le_trans (norm_nonneg _) h1)
    _ = A * ((2 + |s.re|) * Real.exp (s.re / 2)) * ‖s‖ := by ring
    _ ≤ A * (4 * Real.exp (s.re / 4)) * ‖s‖ := by
        apply mul_le_mul_of_nonneg_right _ hnpos.le
        exact mul_le_mul_of_nonneg_left h3 hA
    _ = _ := by ring

/- English proof (translation)
Rewrite using `[norm_quot hx]`. Establish `hn : |s.re| ≤ ‖s‖` using `Complex.abs_re_le_norm s`. Establish `hre : 1 ≤ |s.re|` using `by rw [abs_of_nonpos (by linarith)]; linarith`. Establish `hn1 : 1 ≤ ‖s‖` using `by linarith`. Establish `hxp : 0 ≤ x ^ s.re` using `Real.rpow_nonneg (by linarith) _`.

Establish `h1 : ‖g‖ ≤ A * (1 + |s.re| + B)`. Use `hg.trans (mul_le_mul_of_nonneg_left (by linarith) hA)` and prove the remaining obligations. Establish `h2` using `rpow_le_exp_half hx (show s.re ≤ 0 by linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma left_bound {g s : ℂ} {A x B : ℝ} (hA : 0 ≤ A) (hx : 2 ≤ x) (hs : s.re ≤ -1)
    (hB : |s.im| ≤ B) (hg : ‖g‖ ≤ A * (1 + |s.re| + |s.im|)) :
    ‖g * (x : ℂ) ^ s / s‖ ≤ A * (1 + |s.re| + B) * Real.exp (s.re / 2) := by
  rw [norm_quot hx]
  have hn : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hre : 1 ≤ |s.re| := by rw [abs_of_nonpos (by linarith)]; linarith
  have hn1 : 1 ≤ ‖s‖ := by linarith
  have hxp : 0 ≤ x ^ s.re := Real.rpow_nonneg (by linarith) _
  have h1 : ‖g‖ ≤ A * (1 + |s.re| + B) := by
    refine hg.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  have h2 := rpow_le_exp_half hx (show s.re ≤ 0 by linarith)
  calc ‖g‖ * x ^ s.re / ‖s‖ ≤ ‖g‖ * x ^ s.re :=
        div_le_self (mul_nonneg (norm_nonneg _) hxp) hn1
    _ ≤ _ := mul_le_mul h1 h2 hxp (le_trans (norm_nonneg _) h1)

/- English proof (translation)
Establish `hd : ∀ σ ∈ Set.uIcc (-R) (-(1 / 2) : ℝ), HasDerivAt (fun σ : ℝ => 4 * Real.exp (σ / 4)) (Real.exp (σ / 4)) σ`. Introduce `σ _`. Establish `h` using `((hasDerivAt_id' σ).div_const 4).exp.const_mul 4`. Conclude with `h.congr_deriv (by ring)`. Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((Real.continuous_exp.comp (continuous_id.div_const 4)).intervalIntegrable _ _)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma integral_exp_quarter {R : ℝ} :
    ∫ σ : ℝ in (-R)..(-(1 / 2)), Real.exp (σ / 4)
      = 4 * (Real.exp (-(1 / 2) / 4) - Real.exp (-R / 4)) := by
  have hd : ∀ σ ∈ Set.uIcc (-R) (-(1 / 2) : ℝ),
      HasDerivAt (fun σ : ℝ => 4 * Real.exp (σ / 4)) (Real.exp (σ / 4)) σ := by
    intro σ _
    have h := ((hasDerivAt_id' σ).div_const 4).exp.const_mul 4
    exact h.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_id.div_const 4)).intervalIntegrable _ _)]
  ring

/- English proof (translation)
Establish `hle : (-R) ≤ (-(1 / 2) : ℝ)` using `by linarith`. Establish `h1` using `intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f) (g := fun σ => 4 * A * Real.exp (σ / 4)) hle (Eventually.of_forall fun σ hσ => h σ hσ.1.le hσ.2) ((continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 4)) ).intervalIntegrable _ _)`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[intervalIntegral.integral_const_mul, integral_exp_quarter]`. Establish `e1 : Real.exp (-(1 / 2) / 4) ≤ 1` using `Real.exp_le_one_iff.mpr (by norm_num)`.

Establish `e2` using `Real.exp_pos (-R / 4)`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma horiz_integral {f : ℝ → ℂ} {A R : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R)
    (h : ∀ σ : ℝ, -R ≤ σ → σ ≤ -(1 / 2) → ‖f σ‖ ≤ 4 * A * Real.exp (σ / 4)) :
    ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f σ‖ ≤ 16 * A := by
  have hle : (-R) ≤ (-(1 / 2) : ℝ) := by linarith
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f)
    (g := fun σ => 4 * A * Real.exp (σ / 4)) hle
    (Eventually.of_forall fun σ hσ => h σ hσ.1.le hσ.2)
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 4))
      ).intervalIntegrable _ _)
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul, integral_exp_quarter]
  have e1 : Real.exp (-(1 / 2) / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have e2 := Real.exp_pos (-R / 4)
  nlinarith

/- English proof (translation)
Use `⟨32, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `G A x a b hA hx hab ha hb hG`. Establish `hxC : (x : ℂ) ≠ 0`. Establish `: x ≠ 0` using `by linarith`. Conclude with `this` after adjusting the coercions.

Use `set f : ℂ → ℂ := fun s => G s * (x : ℂ) ^ s / s with hf`. Use `set B : ℝ := max |a| |b| with hBdef`. Establish `hB0 : 0 ≤ B` using `(abs_nonneg a).trans (le_max_left _ _)`. Establish `key : ∀ R : ℝ, 1 ≤ R → ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖ ≤ 32 * A + (b - a) * (A * (1 + R + B) * Real.exp (-R / 2))`. Introduce `R hR`.

Establish `H : DifferentiableOn ℂ f (Set.uIcc (-R) (-(1 / 2)) ×ℂ Set.uIcc a b)`. Introduce `s hs`. Rewrite `hs` using `[Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le hab]`. Take `⟨⟨_, h2⟩, ⟨h3, h4⟩⟩` from `hs`. Establish `hs0 : s ≠ 0`.

Introduce `h0`. Rewrite `h2` using `[h0]`. Evaluate the numerical expressions using `at h2`. Establish `hd` using `(hG s h2 h3 h4).1`. Establish `hc : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s` using `(differentiableAt_id).const_cpow (Or.inl hxC)`.

Conclude with `((hd.mul hc).div differentiableAt_id hs0).differentiableWithinAt`. Establish `rect : (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I)) - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I)) + I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)) - I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)) = 0` using `Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨-R, a⟩ ⟨-(1 / 2), b⟩ H`. Establish `horiz : ∀ τ : ℝ, a ≤ τ → τ ≤ b → 1 ≤ |τ| → ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + τ * I)‖ ≤ 16 * A`. Introduce `τ h1 h2 h3`. Use `horiz_integral hA hR fun σ _ hσ => ?_` and prove the remaining obligations.

Establish `hre : ((σ : ℂ) + τ * I).re = σ` using `by simp`. Establish `him : ((σ : ℂ) + τ * I).im = τ` using `by simp`. Establish `hg` using `(hG (σ + τ * I) (by rw [hre]; exact hσ) (by rw [him]; exact h1) (by rw [him]; exact h2)).2`. Use `horiz_bound (s := (σ : ℂ) + τ * I) hA hx (by rw [hre]; linarith) (by rw [him]; exact h3) hg` as an intermediate fact. Rewrite `this` using `[hre]`. Then use the resulting hypothesis.

Establish `hleft : ‖∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)‖ ≤ (b - a) * (A * (1 + R + B) * Real.exp (-R / 2))`. Establish `h1` using `intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := fun t : ℝ => f (((-R : ℝ) : ℂ) + t * I)) (C := A * (1 + R + B) * Real.exp (-R / 2)) ?_`. Rewrite `h1` using `[abs_of_nonneg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `t ht`.

Rewrite `ht` using `[Set.uIoc_of_le hab]`. Establish `hre : (((-R : ℝ) : ℂ) + t * I).re = -R` using `by simp`. Establish `him : (((-R : ℝ) : ℂ) + t * I).im = t` using `by simp`. Establish `hg` using `(hG (((-R : ℝ) : ℂ) + t * I) (by rw [hre]; linarith) (by rw [him]; exact ht.1.le) (by rw [him]; exact ht.2)).2`. Establish `htB : |t| ≤ B`.

Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion. Use `neg_abs_le a` as an intermediate fact. Use `le_max_left |a| |b|` as an intermediate fact. Combine the linear relations using `[ht.1]`.

Use `le_abs_self b` as an intermediate fact. Use `le_max_right |a| |b|` as an intermediate fact. Combine the linear relations using `[ht.2]`. Use `left_bound (s := ((-R : ℝ) : ℂ) + t * I) (B := B) hA hx (by rw [hre]; linarith) (by rw [him]; exact htB) hg` as an intermediate fact. Rewrite `this` using `[hre, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R)]`.

Conclude with `this`. Establish `hI : ‖I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I))‖ = ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖`. Rewrite using `[norm_smul, Complex.norm_I, one_mul]`. Establish `hI' : ‖I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))‖ = ‖∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)‖`. Rewrite using `[norm_smul, Complex.norm_I, one_mul]`.

Establish `heq : I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)) = (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I)) - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I)) + I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))`. Take the linear combination `rect`. Establish `hha` using `horiz a le_rfl hab ha`. Establish `hhb` using `horiz b hab le_rfl hb`. Rewrite using `[← hI, heq]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `norm_sub_le _ _`. Use `_ ≤ _ := by rw [hI']; linarith`. Establish `hlim : Tendsto (fun u : ℝ => 32 * A + (b - a) * (A * (1 + 2 * u + B) * Real.exp (-(2 * u) / 2))) atTop (𝓝 (32 * A))`. Establish `e0 : Tendsto (fun u : ℝ => u ^ 0 * Real.exp (-u)) atTop (𝓝 0)` using `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0`.

Establish `e1 : Tendsto (fun u : ℝ => u ^ 1 * Real.exp (-u)) atTop (𝓝 0)` using `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1`. Establish `h` using `((e0.const_mul (1 + B)).add (e1.const_mul 2)).const_mul ((b - a) * A)`. Establish `h'` using `h.const_add (32 * A)`. Simplify using `only [mul_zero, add_zero] at h'`. Use `h'.congr fun u => ?_` and prove the remaining obligations.

Establish `: -(2 * u) / 2 = -u` using `by ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hev : ∀ᶠ u : ℝ in atTop, ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖ ≤ 32 * A + (b - a) * (A * (1 + 2 * u + B) * Real.exp (-(2 * u) / 2))` using `by filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu`. Conclude with `key (2 * u) (by linarith)`.

Conclude with `ge_of_tendsto hlim hev`.
-/
theorem main : ∃ K : ℝ, 0 < K ∧ ∀ (G : ℂ → ℂ) (A x a b : ℝ), 0 ≤ A → 2 ≤ x → a ≤ b → 1 ≤ |a| → 1 ≤ |b| → (∀ s : ℂ, s.re ≤ -(1 / 2) → a ≤ s.im → s.im ≤ b → DifferentiableAt ℂ G s ∧ ‖G s‖ ≤ A * (1 + |s.re| + |s.im|)) → ‖∫ t : ℝ in a..b, G (((-(1/2) : ℝ) : ℂ) + t * I) * (x : ℂ) ^ (((-(1/2) : ℝ) : ℂ) + t * I) / (((-(1/2) : ℝ) : ℂ) + t * I)‖ ≤ K * A := by
  refine ⟨32, by norm_num, ?_⟩
  intro G A x a b hA hx hab ha hb hG
  have hxC : (x : ℂ) ≠ 0 := by
    have : x ≠ 0 := by linarith
    exact_mod_cast this
  set f : ℂ → ℂ := fun s => G s * (x : ℂ) ^ s / s with hf
  set B : ℝ := max |a| |b| with hBdef
  have hB0 : 0 ≤ B := (abs_nonneg a).trans (le_max_left _ _)
  have key : ∀ R : ℝ, 1 ≤ R →
      ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖
        ≤ 32 * A + (b - a) * (A * (1 + R + B) * Real.exp (-R / 2)) := by
    intro R hR
    have H : DifferentiableOn ℂ f
        (Set.uIcc (-R) (-(1 / 2)) ×ℂ Set.uIcc a b) := by
      intro s hs
      rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le hab] at hs
      obtain ⟨⟨_, h2⟩, ⟨h3, h4⟩⟩ := hs
      have hs0 : s ≠ 0 := by
        intro h0
        rw [h0] at h2
        norm_num at h2
      have hd := (hG s h2 h3 h4).1
      have hc : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
        (differentiableAt_id).const_cpow (Or.inl hxC)
      exact ((hd.mul hc).div differentiableAt_id hs0).differentiableWithinAt
    have rect : (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I))
        - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I))
        + I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I))
        - I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)) = 0 :=
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨-R, a⟩ ⟨-(1 / 2), b⟩ H
    have horiz : ∀ τ : ℝ, a ≤ τ → τ ≤ b → 1 ≤ |τ| →
        ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + τ * I)‖ ≤ 16 * A := by
      intro τ h1 h2 h3
      refine horiz_integral hA hR fun σ _ hσ => ?_
      have hre : ((σ : ℂ) + τ * I).re = σ := by simp
      have him : ((σ : ℂ) + τ * I).im = τ := by simp
      have hg := (hG (σ + τ * I) (by rw [hre]; exact hσ) (by rw [him]; exact h1)
        (by rw [him]; exact h2)).2
      have := horiz_bound (s := (σ : ℂ) + τ * I) hA hx (by rw [hre]; linarith)
        (by rw [him]; exact h3) hg
      rwa [hre] at this
    have hleft : ‖∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)‖
        ≤ (b - a) * (A * (1 + R + B) * Real.exp (-R / 2)) := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
        (f := fun t : ℝ => f (((-R : ℝ) : ℂ) + t * I))
        (C := A * (1 + R + B) * Real.exp (-R / 2)) ?_
      · rw [abs_of_nonneg (by linarith)] at h1
        linarith
      · intro t ht
        rw [Set.uIoc_of_le hab] at ht
        have hre : (((-R : ℝ) : ℂ) + t * I).re = -R := by simp
        have him : (((-R : ℝ) : ℂ) + t * I).im = t := by simp
        have hg := (hG (((-R : ℝ) : ℂ) + t * I) (by rw [hre]; linarith)
          (by rw [him]; exact ht.1.le) (by rw [him]; exact ht.2)).2
        have htB : |t| ≤ B := by
          rw [abs_le]
          constructor
          · have := neg_abs_le a
            have := le_max_left |a| |b|
            linarith [ht.1]
          · have := le_abs_self b
            have := le_max_right |a| |b|
            linarith [ht.2]
        have := left_bound (s := ((-R : ℝ) : ℂ) + t * I) (B := B) hA hx
          (by rw [hre]; linarith) (by rw [him]; exact htB) hg
        rw [hre, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R)] at this
        exact this
    have hI : ‖I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I))‖
        = ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    have hI' : ‖I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))‖
        = ‖∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    have heq : I • (∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I))
        = (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I))
          - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I))
          + I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I)) := by
      linear_combination rect
    have hha := horiz a le_rfl hab ha
    have hhb := horiz b hab le_rfl hb
    rw [← hI, heq]
    calc _ ≤ ‖(∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I))
            - (∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I))‖
            + ‖I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))‖ := norm_add_le _ _
      _ ≤ ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + b * I)‖
            + ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f (σ + a * I)‖
            + ‖I • (∫ t : ℝ in a..b, f (((-R : ℝ) : ℂ) + t * I))‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by rw [hI']; linarith
  have hlim : Tendsto (fun u : ℝ => 32 * A + (b - a) * (A * (1 + 2 * u + B) * Real.exp (-(2 * u) / 2)))
      atTop (𝓝 (32 * A)) := by
    have e0 : Tendsto (fun u : ℝ => u ^ 0 * Real.exp (-u)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
    have e1 : Tendsto (fun u : ℝ => u ^ 1 * Real.exp (-u)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h := ((e0.const_mul (1 + B)).add (e1.const_mul 2)).const_mul ((b - a) * A)
    have h' := h.const_add (32 * A)
    simp only [mul_zero, add_zero] at h'
    refine h'.congr fun u => ?_
    have : -(2 * u) / 2 = -u := by ring
    rw [this]
    ring
  have hev : ∀ᶠ u : ℝ in atTop,
      ‖∫ t : ℝ in a..b, f (((-(1/2) : ℝ) : ℂ) + t * I)‖
        ≤ 32 * A + (b - a) * (A * (1 + 2 * u + B) * Real.exp (-(2 * u) / 2)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    exact key (2 * u) (by linarith)
  exact ge_of_tendsto hlim hev

end GlobalTheory.CompanionTheory.ExplZeta.LeftShift
