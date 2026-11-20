import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.Mobius

/- English proof (translation)
Introduce `h0`. Establish `him` using `congrArg Complex.im h0`. Establish `hre` using `congrArg Complex.re h0`. Simplify using `at him hre`. Break down `him with hc | hτ` into its components or cases.

Substitute `hc` using the available equality. Establish `hd : d = 0` using `by simpa using hre`. Substitute `hd` using the available equality. Simplify using `at hdet`. Conclude with `h.ne' hτ`.
-/
theorem den_ne (a b c d : ℝ) (hdet : a * d - b * c = 1) (τ : ℂ) (h : 0 < τ.im) :
    (c : ℂ) * τ + d ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  rcases him with hc | hτ
  · subst hc
    have hd : d = 0 := by simpa using hre
    subst hd
    simp at hdet
  · exact h.ne' hτ

/- English proof (translation)
Rewrite using `[Complex.div_im, ← Complex.normSq_eq_norm_sq, ← sub_div]`. Use `congr 1`. Simplify using the standard rewrite rules. Take the linear combination `τ.im * hdet`.
-/
theorem im_frac (a b c d : ℝ) (hdet : a * d - b * c = 1) (τ : ℂ) (h : 0 < τ.im) :
    (((a : ℂ) * τ + b) / ((c : ℂ) * τ + d)).im = τ.im / ‖(c : ℂ) * τ + d‖ ^ 2 := by
  rw [Complex.div_im, ← Complex.normSq_eq_norm_sq, ← sub_div]
  congr 1
  simp
  linear_combination τ.im * hdet

/- English proof (translation)
Establish `h'` using `den_ne a' b' c' d' hdet' τ h`. Establish `hX : 0 < (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')).im`. Rewrite using `[im_frac a' b' c' d' hdet' τ h]`. Establish `: 0 < ‖(c' : ℂ) * τ + d'‖` using `norm_pos_iff.mpr h'`. Check the signs of the components of the expression.

Establish `h2` using `den_ne a b c d hdet _ hX`. Establish `e1 : (c : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + d = (((c * a' + d * c' : ℝ) : ℂ) * τ + ((c * b' + d * d' : ℝ) : ℂ)) / ((c' : ℂ) * τ + d')`. Rewrite using `[eq_div_iff h', add_mul, mul_assoc, div_mul_cancel₀ _ h']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : (a : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + b = (((a * a' + b * c' : ℝ) : ℂ) * τ + ((a * b' + b * d' : ℝ) : ℂ)) / ((c' : ℂ) * τ + d')`. Rewrite using `[eq_div_iff h', add_mul, mul_assoc, div_mul_cancel₀ _ h']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, div_div_div_cancel_right₀ h']`.
-/
theorem comp_frac (a b c d a' b' c' d' : ℝ) (hdet : a * d - b * c = 1)
    (hdet' : a' * d' - b' * c' = 1) (τ : ℂ) (h : 0 < τ.im) :
    (((a * a' + b * c' : ℝ) : ℂ) * τ + ((a * b' + b * d' : ℝ) : ℂ)) /
        (((c * a' + d * c' : ℝ) : ℂ) * τ + ((c * b' + d * d' : ℝ) : ℂ)) =
      ((a : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + b) /
        ((c : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + d) := by
  have h' := den_ne a' b' c' d' hdet' τ h
  have hX : 0 < (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')).im := by
    rw [im_frac a' b' c' d' hdet' τ h]
    have : 0 < ‖(c' : ℂ) * τ + d'‖ := norm_pos_iff.mpr h'
    positivity
  have h2 := den_ne a b c d hdet _ hX
  have e1 : (c : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + d =
      (((c * a' + d * c' : ℝ) : ℂ) * τ + ((c * b' + d * d' : ℝ) : ℂ)) / ((c' : ℂ) * τ + d') := by
    rw [eq_div_iff h', add_mul, mul_assoc, div_mul_cancel₀ _ h']
    push_cast
    ring
  have e2 : (a : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + b =
      (((a * a' + b * c' : ℝ) : ℂ) * τ + ((a * b' + b * d' : ℝ) : ℂ)) / ((c' : ℂ) * τ + d') := by
    rw [eq_div_iff h', add_mul, mul_assoc, div_mul_cancel₀ _ h']
    push_cast
    ring
  rw [e1, e2, div_div_div_cancel_right₀ h']

variable {F : Type} [Field F]

/- English proof (translation)
Establish `h` using `γ.det_coe`. Rewrite `h` using `[Matrix.det_fin_two]`. Use `congrArg σ h` as an intermediate fact. Simplify using `using this`.
-/
theorem det_emb (σ : F →+* ℝ) (γ : SL(2, F)) :
    σ (γ 0 0) * σ (γ 1 1) - σ (γ 0 1) * σ (γ 1 0) = 1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two] at h
  have := congrArg σ h
  simpa using this

/- English proof (translation)
Introduce `F _ _ ρ τ hτ`. Establish `him : ∀ (γ : SL(2, F)) w, (mob ρ γ τ w).im = (τ w).im / ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ ^ 2` using `fun γ w => im_frac _ _ _ _ (det_emb (ρ w) γ) (τ w) (hτ w)`. Use `⟨fun γ w => ⟨him γ w, ?_⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[him]`. Establish `h1` using `den_ne _ _ _ _ (det_emb (ρ w) γ) (τ w) (hτ w)`.

Establish `: 0 < ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖` using `norm_pos_iff.mpr h1`. Use `hτ w` as an intermediate fact. Check the signs of the components of the expression. Introduce `γ γ'`. Use function extensionality and compare the values at `w`.

Use `comp_frac _ _ _ _ _ _ _ _ (det_emb (ρ w) γ) (det_emb (ρ w) γ') (τ w) (hτ w)` as an intermediate fact. Simplify using `only [mob, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]`. Conclude with `this`. Introduce `b`. Use function extensionality and compare the values at `w`.

Simplify using `[mob, nMat]`. Introduce `a`. Use function extensionality and compare the values at `w`. Establish `ha : (ρ w (a : F) : ℝ) ≠ 0` using `by simp`. Establish `hinv : ρ w ((a⁻¹ : Fˣ) : F) = (ρ w (a : F))⁻¹` using `by simp`.

Establish `hc : ((ρ w (a : F) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast ha`. Simplify using `[mob, mMat, hinv]`. Clear the denominators using the available nonvanishing facts. Use function extensionality and compare the values at `w`. Simplify using `[mob, wMat, neg_div, div_neg]`.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F], ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (τ : InfinitePlace F → ℂ), (∀ w, 0 < (τ w).im) → (∀ (γ : SL(2, F)) w, (mob ρ γ τ w).im = (τ w).im / ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ ^ 2 ∧ 0 < (mob ρ γ τ w).im) ∧ (∀ γ γ' : SL(2, F), mob ρ (γ * γ') τ = mob ρ γ (mob ρ γ' τ)) ∧ (∀ b : F, mob ρ (nMat b) τ = fun w => τ w + (ρ w b : ℝ)) ∧ (∀ a : Fˣ, mob ρ (mMat a) τ = fun w => ((ρ w (a : F) : ℝ) : ℂ) ^ 2 * τ w) ∧ mob ρ wMat τ = fun w => -(τ w)⁻¹ := by
  intro F _ _ ρ τ hτ
  have him : ∀ (γ : SL(2, F)) w, (mob ρ γ τ w).im =
      (τ w).im / ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ ^ 2 := fun γ w =>
    im_frac _ _ _ _ (det_emb (ρ w) γ) (τ w) (hτ w)
  refine ⟨fun γ w => ⟨him γ w, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [him]
    have h1 := den_ne _ _ _ _ (det_emb (ρ w) γ) (τ w) (hτ w)
    have : 0 < ‖((ρ w (γ 1 0) : ℝ) : ℂ) * τ w + (ρ w (γ 1 1) : ℝ)‖ := norm_pos_iff.mpr h1
    have := hτ w
    positivity
  · intro γ γ'
    funext w
    have := comp_frac _ _ _ _ _ _ _ _ (det_emb (ρ w) γ) (det_emb (ρ w) γ') (τ w) (hτ w)
    simp only [mob, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
    exact this
  · intro b
    funext w
    simp [mob, nMat]
  · intro a
    funext w
    have ha : (ρ w (a : F) : ℝ) ≠ 0 := by simp
    have hinv : ρ w ((a⁻¹ : Fˣ) : F) = (ρ w (a : F))⁻¹ := by simp
    have hc : ((ρ w (a : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
    simp [mob, mMat, hinv]
    field_simp
  · funext w
    simp [mob, wMat, neg_div, div_neg]

end GlobalTheory.CompanionTheory.SW.Core.Mobius
