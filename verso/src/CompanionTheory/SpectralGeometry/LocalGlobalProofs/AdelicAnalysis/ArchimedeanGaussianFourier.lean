import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealGaussianFourierTransformStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GaussFou

def g1 {ι : Type} [Fintype ι] (S P : Matrix ι ι ℝ) (τ : ℂ) (x : ι → ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) -
    (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ))

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Simplify using `only [gauss, g1, Complex.exp_sum]`.
-/
theorem gauss_eq_prod (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ) :
    gauss B ρ P τ x = ∏ w, g1 (B.map (ρ w)) (P w) (τ w) (x w) := by
  simp only [gauss, g1, Complex.exp_sum]

/- English proof (translation)
Establish `hne : τ ≠ 0` using `fun h0 => by simp [h0] at h`. Rewrite using `[Complex.neg_im, Complex.inv_im, neg_div, neg_neg]`. Conclude with `div_pos h (Complex.normSq_pos.2 hne)`.
-/
theorem neg_inv_im_pos {τ : ℂ} (h : 0 < τ.im) : 0 < (-τ⁻¹).im := by
  have hne : τ ≠ 0 := fun h0 => by simp [h0] at h
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos h (Complex.normSq_pos.2 hne)

/- English proof (translation)
The claim follows from `|((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ w, |ρ w a| := by have h := InfinitePlace.prod_eq_abs_norm a rw [show |((Algebra.norm ℚ a : ℚ) : ℝ)| = ((|Algebra.norm ℚ a| : ℚ) : ℝ) by push_cast; rfl, ← h] refine Finset.prod_congr rfl fun w _ => ?_ have hw : w.mult = 1 := InfinitePlace.mult_is …`.
-/
theorem abs_norm_eq_prod (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : F) :
    |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ w, |ρ w a| := by
  have h := InfinitePlace.prod_eq_abs_norm a
  rw [show |((Algebra.norm ℚ a : ℚ) : ℝ)| = ((|Algebra.norm ℚ a| : ℚ) : ℝ) by push_cast; rfl, ← h]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.mult = 1 := InfinitePlace.mult_isReal ⟨w, hF.isReal w⟩
  rw [hw, pow_one, ← InfinitePlace.norm_embedding_eq, ← hρ, Complex.norm_real, Real.norm_eq_abs]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, Real.sqrt_mul (abs_nonneg _), ih]`.
-/
theorem sqrt_prod_abs {α : Type} (s : Finset α) (f : α → ℝ) :
    Real.sqrt (∏ w ∈ s, |f w|) = ∏ w ∈ s, Real.sqrt |f w| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Real.sqrt_mul (abs_nonneg _), ih]

/- English proof (translation)
Rewrite using `[abs_norm_eq_prod hF ρ hρ, sqrt_prod_abs]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem sqrt_norm_det (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (hF : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| = ∏ w, Real.sqrt |(B.map (ρ w)).det| := by
  rw [abs_norm_eq_prod hF ρ hρ, sqrt_prod_abs]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [RingHom.map_det]
  rfl

/- English proof (translation)
Introduce `F _ _ ι _ _ M B ρ P hQ τ hτ`. Take `⟨hF, hcard, hsym, hdet, hρ, hP, hrel⟩` from `hQ`. Establish `hdetw : ∀ w, (B.map (ρ w)).det ≠ 0` using `fun w => by`. Establish `: (B.map (ρ w)).det = ρ w B.det` using `by rw [RingHom.map_det]; rfl`. Rewrite using `[this]`.

Conclude with `(map_ne_zero (ρ w)).2 hdet`. Establish `one` using `fun w => GlobalTheory.T.real_gaussian_fourier_transform ι (B.map (ρ w)) (P w) (hsym.map _) (hdetw w) (hP w) (hrel w)`. Use `choose c hc using one`. Establish `hfou : ∀ σ : InfinitePlace F → ℂ, (∀ w, 0 < (σ w).im) → ∀ y : InfinitePlace F → ι → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x, gauss B ρ P σ x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) = ∏ w, (c w (σ w) * …`. Introduce `σ hσ y`.

Establish `hint : ∀ x : InfinitePlace F → ι → ℝ, gauss B ρ P σ x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) = ∏ w, (g1 (B.map (ρ w)) (P w) (σ w) (x w) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)))`. Introduce `x`. Rewrite using `[gauss_eq_prod, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, Finset.prod_mul_distrib]`. Repeatedly rewrite using `[hint]`. Rewrite using `[integral_fintype_prod_volume_eq_prod (f := fun w (x : ι → ℝ) => g1 (B.map (ρ w)) (P w) (σ w) x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))), sqrt_norm_det B ρ hF hρ, Complex.ofReal_prod, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Conclude with `(hc w (σ w) (hσ w)).2.2.2 (y w)`. Establish `hcG : ∀ σ : InfinitePlace F → ℂ, (∀ w, 0 < (σ w).im) → cG B ρ P σ = ∏ w, c w (σ w)`. Introduce `σ hσ`. Establish `h0` using `hfou σ hσ 0`.

Simplify `h0` using `[cG, g1]`. Establish `hσ' : ∀ w, 0 < (-(τ w)⁻¹).im` using `fun w => neg_inv_im_pos (hτ w)`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: gauss B ρ P τ = fun x => ∏ w, g1 (B.map (ρ w)) (P w) (τ w) (x w)`. Use function extensionality and compare the values at `fun x => gauss_eq_prod B ρ P τ x`.

Rewrite using `[this]`. Conclude with `Integrable.fintype_prod (f := fun w => g1 (B.map (ρ w)) (P w) (τ w)) fun w => (hc w (τ w) (hτ w)).2.2.1`. Rewrite using `[hcG τ hτ, norm_prod, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[(hc w (τ w) (hτ w)).1, hcard, pow_mul, Real.sq_sqrt (norm_nonneg _)]`.

Rewrite using `[hcG τ hτ, hcG _ hσ', ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun w _ => (hc w (τ w) (hτ w)).2.1`. Introduce `y`. Rewrite using `[hfou τ hτ y, hcG τ hτ, gauss_eq_prod, Finset.prod_mul_distrib]`.
-/
theorem gauss_fourier : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → Integrable (gauss B ρ P τ) ∧ ‖cG B ρ P τ‖ = (∏ w, ‖τ w‖ ^ M)⁻¹ ∧ cG B ρ P τ * cG B ρ P (fun w => -(τ w)⁻¹) = 1 ∧ ∀ y : InfinitePlace F → ι → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x, gauss B ρ P τ x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) y := by
  intro F _ _ ι _ _ M B ρ P hQ τ hτ
  obtain ⟨hF, hcard, hsym, hdet, hρ, hP, hrel⟩ := hQ
  have hdetw : ∀ w, (B.map (ρ w)).det ≠ 0 := fun w => by
    have : (B.map (ρ w)).det = ρ w B.det := by rw [RingHom.map_det]; rfl
    rw [this]
    exact (map_ne_zero (ρ w)).2 hdet
  have one := fun w => GlobalTheory.T.real_gaussian_fourier_transform ι (B.map (ρ w)) (P w) (hsym.map _) (hdetw w) (hP w) (hrel w)
  choose c hc using one
  have hfou : ∀ σ : InfinitePlace F → ℂ, (∀ w, 0 < (σ w).im) → ∀ y : InfinitePlace F → ι → ℝ,
      ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x, gauss B ρ P σ x *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) =
      ∏ w, (c w (σ w) * g1 (B.map (ρ w)) (P w) (-(σ w)⁻¹) (y w)) := by
    intro σ hσ y
    have hint : ∀ x : InfinitePlace F → ι → ℝ, gauss B ρ P σ x *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) =
        ∏ w, (g1 (B.map (ρ w)) (P w) (σ w) (x w) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))) := by
      intro x
      rw [gauss_eq_prod, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, Finset.prod_mul_distrib]
    simp_rw [hint]
    rw [integral_fintype_prod_volume_eq_prod
      (f := fun w (x : ι → ℝ) => g1 (B.map (ρ w)) (P w) (σ w) x *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))),
      sqrt_norm_det B ρ hF hρ, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact (hc w (σ w) (hσ w)).2.2.2 (y w)
  have hcG : ∀ σ : InfinitePlace F → ℂ, (∀ w, 0 < (σ w).im) → cG B ρ P σ = ∏ w, c w (σ w) := by
    intro σ hσ
    have h0 := hfou σ hσ 0
    simpa [cG, g1] using h0
  have hσ' : ∀ w, 0 < (-(τ w)⁻¹).im := fun w => neg_inv_im_pos (hτ w)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : gauss B ρ P τ = fun x => ∏ w, g1 (B.map (ρ w)) (P w) (τ w) (x w) :=
      funext fun x => gauss_eq_prod B ρ P τ x
    rw [this]
    exact Integrable.fintype_prod (f := fun w => g1 (B.map (ρ w)) (P w) (τ w))
      fun w => (hc w (τ w) (hτ w)).2.2.1
  · rw [hcG τ hτ, norm_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(hc w (τ w) (hτ w)).1, hcard, pow_mul, Real.sq_sqrt (norm_nonneg _)]
  · rw [hcG τ hτ, hcG _ hσ', ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun w _ => (hc w (τ w) (hτ w)).2.1
  · intro y
    rw [hfou τ hτ y, hcG τ hτ, gauss_eq_prod, Finset.prod_mul_distrib]

end GlobalTheory.CompanionTheory.SW.GaussFou
