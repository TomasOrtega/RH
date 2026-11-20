import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalDependsOnValueAtZeroStatement

open scoped FourierTransform SchwartzMap InnerProductSpace
open MeasureTheory

namespace GlobalTheory.TransInvSchwartz

/- English proof (translation)
Rewrite using `[SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]`. Simplify using `only [SchwartzMap.compSubConstCLM_apply, smul_eq_mul]`. Rewrite using `[← integral_add_right_eq_self (fun v => Complex.exp (↑(-2 * Real.pi * ⟪v, ξ⟫_ℝ) * Complex.I) * h (v - w)) w]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only [add_sub_cancel_right, GlobalTheory.ArchSch.ech, inner_add_left]`.

Rewrite using `[← mul_assoc, ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourier_compSubConst {n : ℕ} (h : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (w ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (SchwartzMap.compSubConstCLM ℂ w h) ξ = GlobalTheory.ArchSch.ech ⟪w, ξ⟫_ℝ * 𝓕 h ξ := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  simp only [SchwartzMap.compSubConstCLM_apply, smul_eq_mul]
  rw [← integral_add_right_eq_self (fun v => Complex.exp (↑(-2 * Real.pi * ⟪v, ξ⟫_ℝ) * Complex.I) * h (v - w)) w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [add_sub_cancel_right, GlobalTheory.ArchSch.ech, inner_add_left]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/- English proof (translation)
Use `set T := toEuclidean (E := V)`. Use `set C := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T.symm with hC`. Set `Ci` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T`. Establish `hCi : ∀ h, Ci (C h) = h` using `fun h => by ext x; simp [Ci, C]`. Set `Fe` to `SchwartzMap.fourierTransformCLE ℂ (E := 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ))`.

Establish `hFe : ∀ h, Fe h = 𝓕 h` using `fun h => rfl`. Set `ℓ : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ) →L[ℂ] ℂ` to `μ.comp (Ci.comp (Fe.symm : _ →L[ℂ] _))`. Establish `hℓ : ∀ h, ℓ (𝓕 (C h)) = μ h` using `fun h => by show μ (Ci (Fe.symm (Fe (C h)))) = μ h`. Rewrite using `[ContinuousLinearEquiv.symm_apply_apply, hCi]`. Establish `hinv : ∀ L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →ₗ[ℝ] ℝ, ∀ F G : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ), ⇑G = (fun x => GlobalTheory.ArchSch.ech (L x) * F x) → ℓ G = ℓ F`.

Introduce `L F G hG`. Use `set w := (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap L)`. Establish `hw : ∀ x, L x = ⟪w, x⟫_ℝ` using `fun x => by`. Rewrite using `[InnerProductSpace.toDual_symm_apply]`. Both sides reduce to the same expression.

Use `set h := Fe.symm F`. Establish `hF : 𝓕 h = F` using `Fe.apply_symm_apply F`. Establish `hG' : Fe (SchwartzMap.compSubConstCLM ℂ w h) = G`. Use extensionality with `ξ`. Rewrite using `[hFe, fourier_compSubConst, hG, ← hF]`.

Simplify using `only [hw]`. Use `show μ (Ci (Fe.symm G)) = μ (Ci (Fe.symm F))`. Rewrite using `[← hG', ContinuousLinearEquiv.symm_apply_apply]`. Apply `hμ (-T.symm w)` to reduce the goal to its premises. Use extensionality with `x`.

Simplify using `only [Ci, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]`. Rewrite using `[SchwartzMap.compSubConstCLM_apply, map_add, map_neg, ContinuousLinearEquiv.apply_symm_apply, sub_eq_add_neg]`. Use `GlobalTheory.T.schwartz_functional_depends_on_value_at_zero ℓ hinv (𝓕 (C f)) (𝓕 (C g)) hfg` as an intermediate fact. Rewrite `this` using `[hℓ, hℓ]`. Then use the resulting hypothesis.
-/
theorem eq_of_fourier_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hμ : ∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ g = μ f)
    (f g : SchwartzMap V ℂ)
    (hfg : 𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (toEuclidean (E := V)).symm f) 0 =
      𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (toEuclidean (E := V)).symm g) 0) :
    μ f = μ g := by
  set T := toEuclidean (E := V)
  set C := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T.symm with hC
  let Ci := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  have hCi : ∀ h, Ci (C h) = h := fun h => by ext x; simp [Ci, C]
  let Fe := SchwartzMap.fourierTransformCLE ℂ (E := 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ))
  have hFe : ∀ h, Fe h = 𝓕 h := fun h => rfl
  let ℓ : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ) →L[ℂ] ℂ :=
    μ.comp (Ci.comp (Fe.symm : _ →L[ℂ] _))
  have hℓ : ∀ h, ℓ (𝓕 (C h)) = μ h := fun h => by
    show μ (Ci (Fe.symm (Fe (C h)))) = μ h
    rw [ContinuousLinearEquiv.symm_apply_apply, hCi]
  have hinv : ∀ L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →ₗ[ℝ] ℝ, ∀ F G : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ),
      ⇑G = (fun x => GlobalTheory.ArchSch.ech (L x) * F x) → ℓ G = ℓ F := by
    intro L F G hG
    set w := (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap L)
    have hw : ∀ x, L x = ⟪w, x⟫_ℝ := fun x => by
      rw [InnerProductSpace.toDual_symm_apply]; rfl
    set h := Fe.symm F
    have hF : 𝓕 h = F := Fe.apply_symm_apply F
    have hG' : Fe (SchwartzMap.compSubConstCLM ℂ w h) = G := by
      ext ξ
      rw [hFe, fourier_compSubConst, hG, ← hF]
      simp only [hw]
    show μ (Ci (Fe.symm G)) = μ (Ci (Fe.symm F))
    rw [← hG', ContinuousLinearEquiv.symm_apply_apply]
    apply hμ (-T.symm w)
    ext x
    simp only [Ci, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rw [SchwartzMap.compSubConstCLM_apply, map_add, map_neg, ContinuousLinearEquiv.apply_symm_apply, sub_eq_add_neg]
  have := GlobalTheory.T.schwartz_functional_depends_on_value_at_zero ℓ hinv (𝓕 (C f)) (𝓕 (C g)) hfg
  rwa [hℓ, hℓ] at this

/- English proof (translation)
Introduce `V _ _ _ μ μ' hμ hμ' h0`. Use `set C := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (toEuclidean (E := V)).symm with hC`. Set `Fe` to `SchwartzMap.fourierTransformCLE ℂ (E := 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ))`. Set `Φ : SchwartzMap V ℂ → ℂ` to `fun f => Fe (C f) 0`. Establish `hΦs : ∀ (c : ℂ) f, Φ (c • f) = c * Φ f` using `fun c f => by show Fe (C (c • f)) 0 = c * Fe (C f) 0`.

Rewrite using `[map_smul, map_smul]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨f₀, hf₀⟩ : ∃ f₀, μ f₀ ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `h0 (ContinuousLinearMap.ext hc)`. Establish `hΦ0 : Φ f₀ ≠ 0`. Introduce `hz`. Apply `hf₀` to reduce the goal to its premises. Rewrite using `[eq_of_fourier_zero μ hμ f₀ 0 (by show Φ f₀ = Fe (C 0) 0`.

Rewrite using `[hz]`. Use the proof step `simp), map_zero]`. Establish `hrep : ∀ ν : SchwartzMap V ℂ →L[ℂ] ℂ, (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → ν g = ν f) → ∀ f, ν f = (Φ f / Φ f₀) * ν f₀` using `fun ν hν f => by`. Rewrite using `[eq_of_fourier_zero ν hν f ((Φ f / Φ f₀) • f₀) (by show Φ f = Φ ((Φ f / Φ f₀) • f₀)`. Rewrite using `[hΦs, div_mul_cancel₀ _ hΦ0]), map_smul, smul_eq_mul]`.

Use `⟨μ' f₀ / μ f₀, ContinuousLinearMap.ext fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.smul_apply, hrep μ' hμ' f, hrep μ hμ f, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem dim_le_one : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ μ' : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ g = μ f) →
    (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ' g = μ' f) →
    μ ≠ 0 → ∃ c : ℂ, μ' = c • μ := by
  intro V _ _ _ μ μ' hμ hμ' h0
  set C := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (toEuclidean (E := V)).symm with hC
  let Fe := SchwartzMap.fourierTransformCLE ℂ (E := 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ))
  let Φ : SchwartzMap V ℂ → ℂ := fun f => Fe (C f) 0
  have hΦs : ∀ (c : ℂ) f, Φ (c • f) = c * Φ f := fun c f => by
    show Fe (C (c • f)) 0 = c * Fe (C f) 0
    rw [map_smul, map_smul]; rfl
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, μ f₀ ≠ 0 := by
    by_contra hc; push_neg at hc; exact h0 (ContinuousLinearMap.ext hc)
  have hΦ0 : Φ f₀ ≠ 0 := by
    intro hz
    apply hf₀
    rw [eq_of_fourier_zero μ hμ f₀ 0 (by
      show Φ f₀ = Fe (C 0) 0
      rw [hz]; simp), map_zero]
  have hrep : ∀ ν : SchwartzMap V ℂ →L[ℂ] ℂ,
      (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → ν g = ν f) →
      ∀ f, ν f = (Φ f / Φ f₀) * ν f₀ := fun ν hν f => by
    rw [eq_of_fourier_zero ν hν f ((Φ f / Φ f₀) • f₀) (by
      show Φ f = Φ ((Φ f / Φ f₀) • f₀)
      rw [hΦs, div_mul_cancel₀ _ hΦ0]), map_smul, smul_eq_mul]
  refine ⟨μ' f₀ / μ f₀, ContinuousLinearMap.ext fun f => ?_⟩
  rw [ContinuousLinearMap.smul_apply, hrep μ' hμ' f, hrep μ hμ f, smul_eq_mul]
  field_simp

end GlobalTheory.TransInvSchwartz
