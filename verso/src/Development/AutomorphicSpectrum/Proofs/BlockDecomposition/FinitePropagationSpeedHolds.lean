import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TranslatedLengthBoundedDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMonotoneCutoffExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRrEqZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeReversalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirRightLaplacianFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyIdentityOfLengthFunctionStatement

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Use `haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))`. Use `haveI : LocallyCompactSpace (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace`. Conclude with `Units.isClosedEmbedding_embedProduct.locallyCompactSpace`.
-/
theorem locCpt (n : ℕ) : LocallyCompactSpace (G n) := by
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

/- English proof (translation)
Use `haveI := locCpt n`. Use `letI : MeasurableSpace (G n) := borel _`. Use `haveI : BorelSpace (G n) := ⟨rfl⟩`. Conclude with `⟨inferInstance, inferInstance, Measure.haar, inferInstance⟩`.
-/
theorem exists_haar (n : ℕ) : ∃ (_ : MeasurableSpace (G n)) (_ : BorelSpace (G n)) (μ : Measure (G n)), μ.IsHaarMeasure := by
  haveI := locCpt n
  letI : MeasurableSpace (G n) := borel _
  haveI : BorelSpace (G n) := ⟨rfl⟩
  exact ⟨inferInstance, inferInstance, Measure.haar, inferInstance⟩

/- English proof (translation)
Introduce `s y hy`. Establish `h` using `hu.2.2.1 s y hy`. Rewrite `h` using `[hA _ (hu.2.1 s) y hy]`. Establish `h2 : dt (dt u) s y = iteratedDeriv 2 (fun r => u r y) s`. Simplify using `only [dt, iteratedDeriv_succ, iteratedDeriv_zero]`.

Rewrite using `[h2, h]`. Establish `: (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem waveEq {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u) (A : E.V →L[ℂ] E.V)
    (hA : ∀ f ∈ CE E, ∀ g ∈ GLs n, Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g)) :
    ∀ s, ∀ y ∈ GLs n, dt (dt u) s y = (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + (A.restrictScalars ℝ) (u s y) := by
  intro s y hy
  have h := hu.2.2.1 s y hy
  rw [hA _ (hu.2.1 s) y hy] at h
  have h2 : dt (dt u) s y = iteratedDeriv 2 (fun r => u r y) s := by
    simp only [dt, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h2, h]
  have : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  rfl

/- English proof (translation)
Take `⟨mG, bG, μ, hμ⟩` from `exists_haar n`. Use `letI : InnerProductSpace ℝ E.V := InnerProductSpace.rclikeToReal ℂ E.V`. Take `⟨A, hA⟩` from `GlobalTheory.T.casimir_right_laplacian_formula E`. Take `⟨l1, l2, l3⟩` from `hlg x hx`. Establish `hxu : IsUnit x.det` using `isUnit_iff_ne_zero.2 hx`.

Establish `hxx : x⁻¹ * x = 1` using `Matrix.nonsing_inv_mul _ hxu`. Establish `hxx' : x * x⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hxu`. Establish `hxi : x⁻¹ ∈ GLs n`. Establish `: x⁻¹.det * x.det = 1` using `by rw [← Matrix.det_mul, hxx, Matrix.det_one]`. Conclude with `left_ne_zero_of_mul_eq_one this |> fun h => h`.

Establish `hmul : ∀ y ∈ GLs n, x⁻¹ * y ∈ GLs n` using `fun y hy => by`. Simplify using `only [GLs, Set.mem_setOf_eq, Matrix.det_mul]`. Conclude with `mul_ne_zero hxi hy`. Establish `hbp : ∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg (x⁻¹ * y) → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0`. Introduce `Ψ hΨ ⟨R, hRΨ⟩ X`.

Use `GlobalTheory.T.integral_right_derivative_zero_alt hR μ Ψ hΨ ⟨R + lg x, fun y hy hlt => hRΨ y hy ?_⟩ X` and prove the remaining obligations. Use `(hL n).1 x hx _ (hmul y hy)` as an intermediate fact. Rewrite `this` using `[← mul_assoc, hxx', one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv` using `GlobalTheory.T.energy_identity_of_length_function (W := E.V) μ (fun y => lg (x⁻¹ * y)) l1 l2 C₁ hC₁ l3 hbp χ h1 h2 h3 h5 u hu.1 (A.restrictScalars ℝ) (waveEq E u hu A hA) C hC (lg (1 : Mat n) + C * t) h4 ?_ ?_ t ht x hx ?_`.

Conclude with `hv`. Introduce `y hy hlt`. Use `h0 (x⁻¹ * y) (hmul y hy) (by have h' : lg (x⁻¹ * y) < lg (1 : Mat n) + C * t + 1 := hlt; linarith)` as an intermediate fact. Rewrite `this` using `[← mul_assoc, hxx', one_mul]`. Then use the resulting hypothesis. Introduce `y hy`.

Conclude with `hu.2.2.2 y hy`. Simplify using `only [hxx]`. Conclude with `le_refl _`.
-/
theorem speed_pos (hL : LgFacts) (hR : RCalc) {n : ℕ} (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hlg : ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧ (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧ ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C₁)
    (χ : ℝ → ℝ) (h1 : ContDiff ℝ ∞ χ) (h2 : ∀ x, deriv χ x ≤ 0) (h3 : ∀ x, 0 ≤ χ x) (h4 : ∀ x, x ≤ 0 → χ x = 1) (h5 : ∀ x, 1 ≤ x → χ x = 0)
    (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u) (t : ℝ) (ht : 0 ≤ t) (x : Mat n) (hx : x ∈ GLs n)
    (C : ℝ) (hC : C₁ * (1 + Fintype.card (Ix n)) ≤ C)
    (h0 : ∀ y ∈ GLs n, lg y ≤ lg (1 : Mat n) + 1 + C * t → u 0 (x * y) = 0) : u t x = 0 := by
  obtain ⟨mG, bG, μ, hμ⟩ := exists_haar n
  letI : InnerProductSpace ℝ E.V := InnerProductSpace.rclikeToReal ℂ E.V
  obtain ⟨A, hA⟩ := GlobalTheory.T.casimir_right_laplacian_formula E
  obtain ⟨l1, l2, l3⟩ := hlg x hx
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have hxx : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul _ hxu
  have hxx' : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv _ hxu
  have hxi : x⁻¹ ∈ GLs n := by
    have : x⁻¹.det * x.det = 1 := by rw [← Matrix.det_mul, hxx, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one this |> fun h => h
  have hmul : ∀ y ∈ GLs n, x⁻¹ * y ∈ GLs n := fun y hy => by
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul]
    exact mul_ne_zero hxi hy
  have hbp : ∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg (x⁻¹ * y) → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
    intro Ψ hΨ ⟨R, hRΨ⟩ X
    refine GlobalTheory.T.integral_right_derivative_zero_alt hR μ Ψ hΨ ⟨R + lg x, fun y hy hlt => hRΨ y hy ?_⟩ X
    have := (hL n).1 x hx _ (hmul y hy)
    rw [← mul_assoc, hxx', one_mul] at this
    linarith
  have hv := GlobalTheory.T.energy_identity_of_length_function (W := E.V) μ (fun y => lg (x⁻¹ * y)) l1 l2 C₁ hC₁ l3 hbp χ h1 h2 h3 h5 u hu.1
    (A.restrictScalars ℝ) (waveEq E u hu A hA) C hC (lg (1 : Mat n) + C * t) h4 ?_ ?_ t ht x hx ?_
  · exact hv
  · intro y hy hlt
    have := h0 (x⁻¹ * y) (hmul y hy) (by have h' : lg (x⁻¹ * y) < lg (1 : Mat n) + C * t + 1 := hlt; linarith)
    rwa [← mul_assoc, hxx', one_mul] at this
  · intro y hy
    exact hu.2.2.2 y hy
  · simp only [hxx]
    exact le_refl _

/- English proof (translation)
Introduce `hL hU hR n`. Take `⟨C₁, hC₁, hlg⟩` from `GlobalTheory.T.translated_length_bounded_derivative hL n`. Take `⟨χ, h1, h2, h3, h4, h5⟩` from `GlobalTheory.T.smooth_monotone_cutoff_exists`. Use `set C := C₁ * (1 + Fintype.card (Ix n)) with hCdef`. Establish `hC0 : 0 ≤ C` using `by positivity`.

Establish `hl0 : 0 ≤ lg (1 : Mat n)`. Unfold `lg`. Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `: 0 ≤ ∑ a, ∑ b, (‖(1 : Mat n) a b‖ ^ 2 + ‖(1 : Mat n)⁻¹ a b‖ ^ 2)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨C + lg (1 : Mat n) + 1, ?_⟩` and prove the remaining obligations. Establish `key : ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ t : ℝ, 0 ≤ t → ∀ x ∈ GLs n, (∀ y ∈ GLs n, lg y ≤ (C + lg (1 : Mat n) + 1) * (1 + t) → u 0 (x * y) = 0) → u t x = 0`. Introduce `E u hu t ht x hx h0`. Use `speed_pos hL hR C₁ hC₁ hlg χ h1 h2 h3 h4 h5 E u hu t ht x hx C le_rfl ?_` and prove the remaining obligations. Introduce `y hy hle`.

Use `h0 y hy (hle.trans ?_)` and prove the remaining obligations. Use polynomial arithmetic with `[mul_nonneg hC0 ht, mul_nonneg hl0 ht]`. Introduce `E u hu t x hx h0`. Break down `le_total 0 t with ht | ht` into its components or cases. Conclude with `key E u hu t ht x hx (by rwa [abs_of_nonneg ht] at h0)`.

Use `key E _ (GlobalTheory.T.wave_time_reversal E u hu) (-t) (by linarith) x hx (by` as an intermediate fact. Introduce `y hy hle`. Simplify using `only [neg_zero]`. Conclude with `h0 y hy (by rwa [abs_of_nonpos ht]))`. Simplify using `using this`.
-/
theorem asmSpeed : AsmSpeed := by
  intro hL hU hR n
  obtain ⟨C₁, hC₁, hlg⟩ := GlobalTheory.T.translated_length_bounded_derivative hL n
  obtain ⟨χ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.smooth_monotone_cutoff_exists
  set C := C₁ * (1 + Fintype.card (Ix n)) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hl0 : 0 ≤ lg (1 : Mat n) := by
    unfold lg
    apply Real.log_nonneg
    have : 0 ≤ ∑ a, ∑ b, (‖(1 : Mat n) a b‖ ^ 2 + ‖(1 : Mat n)⁻¹ a b‖ ^ 2) := by positivity
    linarith
  refine ⟨C + lg (1 : Mat n) + 1, ?_⟩
  have key : ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ t : ℝ, 0 ≤ t → ∀ x ∈ GLs n,
      (∀ y ∈ GLs n, lg y ≤ (C + lg (1 : Mat n) + 1) * (1 + t) → u 0 (x * y) = 0) → u t x = 0 := by
    intro E u hu t ht x hx h0
    refine speed_pos hL hR C₁ hC₁ hlg χ h1 h2 h3 h4 h5 E u hu t ht x hx C le_rfl ?_
    intro y hy hle
    refine h0 y hy (hle.trans ?_)
    nlinarith [mul_nonneg hC0 ht, mul_nonneg hl0 ht]
  intro E u hu t x hx h0
  rcases le_total 0 t with ht | ht
  · exact key E u hu t ht x hx (by rwa [abs_of_nonneg ht] at h0)
  · have := key E _ (GlobalTheory.T.wave_time_reversal E u hu) (-t) (by linarith) x hx (by
      intro y hy hle
      simp only [neg_zero]
      exact h0 y hy (by rwa [abs_of_nonpos ht]))
    simpa using this

end GlobalTheory.CompanionTheory.WaveSpd
