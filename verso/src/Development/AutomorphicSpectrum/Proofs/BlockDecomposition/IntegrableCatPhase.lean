import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GauIntegrable
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval.Ibp

open Ad3 Ad3.LR

def dirY (j : Fin 2) : M23 := fun r c => if r = j ∧ c = 2 then 1 else 0

def phase (ξ y : Fin 2 → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))

/- English proof (translation)
Use function extensionality and compare the values at `r c`. Apply the tactic sequence `fin_cases j <;> fin_cases r <;> fin_cases c <;> simp [cat, dirY]`.
-/
lemma cat_add_smul (A : M22) (y : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    cat A (y + t • Pi.single j (1 : ℝ)) = cat A y + t • dirY j := by
  funext r c
  fin_cases j <;> fin_cases r <;> fin_cases c <;> simp [cat, dirY]

/- English proof (translation)
Use `continuous_pi fun r => continuous_pi fun c => ?_` and prove the remaining obligations. Use `fin_cases c`. Simplify `continuous_const` using `[cat]`. Simplify `continuous_const` using `[cat]`. Simplify `continuous_apply r` using `[cat]`.
-/
lemma continuous_cat (A : M22) : Continuous (cat A) := by
  refine continuous_pi fun r => continuous_pi fun c => ?_
  fin_cases c
  · simpa [cat] using continuous_const
  · simpa [cat] using continuous_const
  · simpa [cat] using continuous_apply r

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_` and prove the remaining obligations. Establish `h1 : ‖cat A y r 2‖ ≤ ‖cat A y r‖` using `norm_le_pi_norm (cat A y r) 2`. Establish `h2 : ‖cat A y r‖ ≤ ‖cat A y‖` using `norm_le_pi_norm (cat A y) r`. Establish `h3 : cat A y r 2 = y r` using `by simp [cat]`. Rewrite `h1` using `[h3]`.

Conclude with `h1.trans h2`.
-/
lemma norm_le_norm_cat (A : M22) (y : Fin 2 → ℝ) : ‖y‖ ≤ ‖cat A y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  have h1 : ‖cat A y r 2‖ ≤ ‖cat A y r‖ := norm_le_pi_norm (cat A y r) 2
  have h2 : ‖cat A y r‖ ≤ ‖cat A y‖ := norm_le_pi_norm (cat A y) r
  have h3 : cat A y r 2 = y r := by simp [cat]
  rw [h3] at h1
  exact h1.trans h2

/- English proof (translation)
Use `set C : ℝ := 2 ^ 3 * ((Finset.Iic ((3, 0) : ℕ × ℕ)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ`. Establish `hint : Integrable (fun y : Fin 2 → ℝ => C * (1 + ‖y‖) ^ (-(3 : ℝ)))` using `(integrable_one_add_norm (by rw [Module.finrank_fin_fun]; norm_num)).const_mul C`. Use `hint.mono' (Φ.continuous.comp (continuous_cat A)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Establish `hb` using `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0)) (k := 3) (n := 0) le_rfl le_rfl Φ (cat A y)`. Rewrite `hb` using `[norm_iteratedFDeriv_zero]`.

Establish `hpos : 0 < (1 + ‖y‖) ^ 3` using `by positivity`. Establish `hle : (1 + ‖y‖) ^ 3 ≤ (1 + ‖cat A y‖) ^ 3`. Use `norm_le_norm_cat A y` as an intermediate fact. Use `gcongr`. Establish `hb' : (1 + ‖y‖) ^ 3 * ‖Φ (cat A y)‖ ≤ C` using `(mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hb`.

Establish `he : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹`. Rewrite using `[Real.rpow_neg (by positivity)]`. Use `norm_cast`. Rewrite using `[he, ← div_eq_mul_inv, le_div_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma integrable_cat (Φ : Sw) (A : M22) : Integrable (fun y : Fin 2 → ℝ => Φ (cat A y)) := by
  set C : ℝ := 2 ^ 3 * ((Finset.Iic ((3, 0) : ℕ × ℕ)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ
  have hint : Integrable (fun y : Fin 2 → ℝ => C * (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm (by rw [Module.finrank_fin_fun]; norm_num)).const_mul C
  refine hint.mono' (Φ.continuous.comp (continuous_cat A)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0)) (k := 3) (n := 0)
    le_rfl le_rfl Φ (cat A y)
  rw [norm_iteratedFDeriv_zero] at hb
  have hpos : 0 < (1 + ‖y‖) ^ 3 := by positivity
  have hle : (1 + ‖y‖) ^ 3 ≤ (1 + ‖cat A y‖) ^ 3 := by
    have := norm_le_norm_cat A y
    gcongr
  have hb' : (1 + ‖y‖) ^ 3 * ‖Φ (cat A y)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hb
  have he : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  rw [he, ← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

/- English proof (translation)
Unfold `phase`. Use `fun_prop`.
-/
lemma continuous_phase (ξ : Fin 2 → ℝ) : Continuous (phase ξ) := by
  unfold phase
  fun_prop

/- English proof (translation)
Unfold `phase`. Establish `: 2 * (Real.pi : ℂ) * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ) = ((2 * Real.pi * (ξ 0 * y 0 + ξ 1 * y 1) : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`.
-/
lemma norm_phase (ξ y : Fin 2 → ℝ) : ‖phase ξ y‖ = 1 := by
  unfold phase
  have : 2 * (Real.pi : ℂ) * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ) =
      ((2 * Real.pi * (ξ 0 * y 0 + ξ 1 * y 1) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Use `(integrable_cat Φ A).mono ((Φ.continuous.comp (continuous_cat A)).mul (continuous_phase ξ)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `[norm_phase]`.
-/
lemma integrable_cat_phase (Φ : Sw) (A : M22) (ξ : Fin 2 → ℝ) :
    Integrable (fun y : Fin 2 → ℝ => Φ (cat A y) * phase ξ y) := by
  refine (integrable_cat Φ A).mono
    ((Φ.continuous.comp (continuous_cat A)).mul (continuous_phase ξ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  simp [norm_phase]

/- English proof (translation)
Establish `h : HasFDerivAt Φ (fderiv ℝ Φ (cat A y)) (cat A y)` using `(Φ.differentiableAt).hasFDerivAt`. Establish `h2` using `h.hasLineDerivAt (dirY j)`. Rewrite using `[SchwartzMap.lineDerivOp_apply_eq_fderiv]`. Unfold `HasLineDerivAt at h2 ⊢`. Establish `e : (fun t : ℝ => Φ (cat A (y + t • Pi.single j (1 : ℝ)))) = fun t : ℝ => Φ (cat A y + t • dirY j)`.

Use function extensionality and compare the values at `t`. Rewrite using `[cat_add_smul]`. Rewrite using `[e]`. Conclude with `h2`.
-/
lemma hasLineDerivAt_cat (Φ : Sw) (A : M22) (j : Fin 2) (y : Fin 2 → ℝ) :
    HasLineDerivAt ℝ (fun y : Fin 2 → ℝ => Φ (cat A y))
      (LineDeriv.lineDerivOp (dirY j) Φ (cat A y)) y (Pi.single j (1 : ℝ)) := by
  have h : HasFDerivAt Φ (fderiv ℝ Φ (cat A y)) (cat A y) :=
    (Φ.differentiableAt).hasFDerivAt
  have h2 := h.hasLineDerivAt (dirY j)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  unfold HasLineDerivAt at h2 ⊢
  have e : (fun t : ℝ => Φ (cat A (y + t • Pi.single j (1 : ℝ)))) =
      fun t : ℝ => Φ (cat A y + t • dirY j) := by
    funext t; rw [cat_add_smul]
  rw [e]
  exact h2

/- English proof (translation)
Apply the tactic sequence `fin_cases j <;> simp <;> ring`.
-/
lemma dot_add_smul (ξ y : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    ξ 0 * (y + t • Pi.single j (1 : ℝ) : Fin 2 → ℝ) 0 + ξ 1 * (y + t • Pi.single j (1 : ℝ) : Fin 2 → ℝ) 1 =
      (ξ 0 * y 0 + ξ 1 * y 1) + t * ξ j := by
  fin_cases j <;> simp <;> ring

/- English proof (translation)
Unfold `HasLineDerivAt`. Use `set a : ℝ := ξ 0 * y 0 + ξ 1 * y 1 with ha`. Use `set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hc`. Establish `e : (fun t : ℝ => phase ξ (y + t • Pi.single j (1 : ℝ))) = fun t : ℝ => Complex.exp (c * ((a + t * ξ j : ℝ) : ℂ))`. Use function extensionality and compare the values at `t`.

Unfold `phase`. Rewrite using `[dot_add_smul]`. Rewrite using `[e]`. Establish `h1 : HasDerivAt (fun t : ℝ => a + t * ξ j) (ξ j) 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).mul_const (ξ j)).const_add a`.

Establish `h2 : HasDerivAt (fun t : ℝ => ((a + t * ξ j : ℝ) : ℂ)) (ξ j : ℂ) 0` using `h1.ofReal_comp`. Establish `h3` using `(h2.const_mul c).cexp`. Establish `e0 : c * ((a + 0 * ξ j : ℝ) : ℂ) = c * (a : ℂ)` using `by simp`. Rewrite `h3` using `[e0]`. Establish `e1 : c * (ξ j : ℂ) * phase ξ y = Complex.exp (c * (a : ℂ)) * (c * (ξ j : ℂ))`.

Unfold `phase`. Rewrite using `[mul_comm]`. Rewrite using `[e1]`. Conclude with `h3`.
-/
lemma hasLineDerivAt_phase (ξ : Fin 2 → ℝ) (j : Fin 2) (y : Fin 2 → ℝ) :
    HasLineDerivAt ℝ (phase ξ) (2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ) * phase ξ y) y
      (Pi.single j (1 : ℝ)) := by
  unfold HasLineDerivAt
  set a : ℝ := ξ 0 * y 0 + ξ 1 * y 1 with ha
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hc
  have e : (fun t : ℝ => phase ξ (y + t • Pi.single j (1 : ℝ))) =
      fun t : ℝ => Complex.exp (c * ((a + t * ξ j : ℝ) : ℂ)) := by
    funext t
    unfold phase
    rw [dot_add_smul]
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => a + t * ξ j) (ξ j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ξ j)).const_add a
  have h2 : HasDerivAt (fun t : ℝ => ((a + t * ξ j : ℝ) : ℂ)) (ξ j : ℂ) 0 := h1.ofReal_comp
  have h3 := (h2.const_mul c).cexp
  have e0 : c * ((a + 0 * ξ j : ℝ) : ℂ) = c * (a : ℂ) := by simp
  rw [e0] at h3
  have e1 : c * (ξ j : ℂ) * phase ξ y = Complex.exp (c * (a : ℂ)) * (c * (ξ j : ℂ)) := by
    unfold phase
    rw [mul_comm]
  rw [e1]
  exact h3

/- English proof (translation)
Use `set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ) with hc`. Use `set Ψ : Sw := LineDeriv.lineDerivOp (dirY j) Φ with hΨ`. Establish `key` using `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := (volume : Measure (Fin 2 → ℝ))) (B := ContinuousLinearMap.mul ℝ ℂ) (f := fun y => Φ (cat A y)) (f' := fun y => Ψ (cat A y)) (g := phase ξ) (g' := fun y => c * phase ξ y) (v := Pi.single j (1 : ℝ)) (integrable_ …`. Use `(integrable_cat_phase Φ A ξ).const_mul c` as an intermediate fact. Use `this.congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `only [ContinuousLinearMap.mul_apply']`. Use the proof step `ring)`. Use the proof step `(integrable_cat_phase Φ A ξ)`. Use the proof step `(fun y _ => hasLineDerivAt_cat Φ A j y)`. Use the proof step `(fun y _ => hasLineDerivAt_phase ξ j y)`.

Simplify using `only [ContinuousLinearMap.mul_apply'] at key`. Establish `e1 : fz Ψ A ξ = ∫ y, Ψ (cat A y) * phase ξ y` using `rfl`. Establish `e2 : fz Φ A ξ = ∫ y, Φ (cat A y) * phase ξ y` using `rfl`. Establish `e3 : ∫ y, Φ (cat A y) * (c * phase ξ y) = c * ∫ y, Φ (cat A y) * phase ξ y`. Rewrite using `[← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`. Rewrite `key` using `[e3]`.

Take the linear combination `key`.
-/
theorem fz_lineDeriv (Φ : Sw) (j : Fin 2) (A : M22) (ξ : Fin 2 → ℝ) :
    fz (LineDeriv.lineDerivOp (dirY j) Φ) A ξ =
      -(2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) * fz Φ A ξ := by
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ) with hc
  set Ψ : Sw := LineDeriv.lineDerivOp (dirY j) Φ with hΨ
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin 2 → ℝ))) (B := ContinuousLinearMap.mul ℝ ℂ)
    (f := fun y => Φ (cat A y)) (f' := fun y => Ψ (cat A y))
    (g := phase ξ) (g' := fun y => c * phase ξ y) (v := Pi.single j (1 : ℝ))
    (integrable_cat_phase Ψ A ξ)
    (by
      have := (integrable_cat_phase Φ A ξ).const_mul c
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [ContinuousLinearMap.mul_apply']
      ring)
    (integrable_cat_phase Φ A ξ)
    (fun y _ => hasLineDerivAt_cat Φ A j y)
    (fun y _ => hasLineDerivAt_phase ξ j y)
  simp only [ContinuousLinearMap.mul_apply'] at key
  have e1 : fz Ψ A ξ = ∫ y, Ψ (cat A y) * phase ξ y := rfl
  have e2 : fz Φ A ξ = ∫ y, Φ (cat A y) * phase ξ y := rfl
  have e3 : ∫ y, Φ (cat A y) * (c * phase ξ y) = c * ∫ y, Φ (cat A y) * phase ξ y := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [e1, e2]
  rw [e3] at key
  linear_combination key

/- English proof (translation)
Introduce `Φ j` and use `⟨LineDeriv.lineDerivOp (dirY j) Φ, fun A ξ => fz_lineDeriv Φ j A ξ⟩`.
-/
theorem main : ∀ (Φ : Ad3.LR.Sw) (j : Fin 2), ∃ Ψ : Ad3.LR.Sw, ∀ (A : Ad3.LR.M22) (ξ : Fin 2 → ℝ),
    GlobalTheory.CompanionTheory.Parseval.fz Ψ A ξ =
      -(2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) * GlobalTheory.CompanionTheory.Parseval.fz Φ A ξ :=
  fun Φ j => ⟨LineDeriv.lineDerivOp (dirY j) Φ, fun A ξ => fz_lineDeriv Φ j A ξ⟩

end GlobalTheory.CompanionTheory.Parseval.Ibp
