import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConvolutionEqDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarGLRealPointsDensityDetInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionLieAlgebraPullbackDetStatement

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

namespace GlobalTheory.GLParametrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Set `L : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a)` to `{ toFun := lmul map_add' := fun x y => ContinuousLinearMap.ext fun z => (Matrix.add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z) : _) map_smul' := fun c x => ContinuousLinearMap.ext fun z => (Matrix.smul_mul c (Matrix.of x) (Matrix.of z) : _) }`. Conclude with `L.continuous_of_finiteDimensional`.
-/
theorem continuous_lmul : Continuous fun x : Lie E a => lmul x := by
  let L : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) :=
    { toFun := lmul
      map_add' := fun x y => ContinuousLinearMap.ext fun z =>
        (Matrix.add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z) : _)
      map_smul' := fun c x => ContinuousLinearMap.ext fun z =>
        (Matrix.smul_mul c (Matrix.of x) (Matrix.of z) : _) }
  exact L.continuous_of_finiteDimensional

/- English proof (translation)
The claim follows from `continuous_abs.comp (ContinuousLinearMap.continuous_det.comp continuous_lmul)`.
-/
theorem continuous_absDet :
    Continuous fun x : Lie E a => |LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)| :=
  continuous_abs.comp (ContinuousLinearMap.continuous_det.comp continuous_lmul)

/- English proof (translation)
Establish `h : ((lmul (toL u.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) ∘ₗ ((lmul (toL (u⁻¹).val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) = LinearMap.id` using `LinearMap.ext fun z => u.mul_inv_cancel_left (Matrix.of z)`. Introduce `h0`. Establish `h1` using `congrArg LinearMap.det h`. Rewrite `h1` using `[LinearMap.det_comp, h0, zero_mul, LinearMap.det_id]`. Conclude with `zero_ne_one h1`.
-/
theorem det_lmul_ne_zero (u : GL (Fin a) (Cinf E)) :
    LinearMap.det ((lmul (toL u.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) ≠ 0 := by
  have h : ((lmul (toL u.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) ∘ₗ
      ((lmul (toL (u⁻¹).val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) = LinearMap.id :=
    LinearMap.ext fun z => u.mul_inv_cancel_left (Matrix.of z)
  intro h0
  have h1 := congrArg LinearMap.det h
  rw [LinearMap.det_comp, h0, zero_mul, LinearMap.det_id] at h1
  exact zero_ne_one h1

end

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `E _ _ _ a ν hν p hp`. Take `⟨d, b, P, hP, hsol, -⟩` from `GlobalTheory.T.laplacianPolynomialKernel_of_polynomial_laplacian E a p hp`. Use `borelize ↥(GlobalTheory.HCA.glG E a)`. Take `⟨μ, hμ, hint⟩` from `GlobalTheory.T.exists_haar_GL_realPoints_density_det_inv E a ν hν`. Use `haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _`.

Take `⟨α₀, hs, -, hc, hα₀⟩` from `@GlobalTheory.T.exists_smooth_convolution_eq_derivative (Matrix (Fin a) (Fin a) (Cinf E)) _ _ _ _ (GlobalTheory.HCA.glG E a) (GlobalTheory.HCA.glL E a) (GlobalTheory.HCA.glH E a) d b P hP _ ⟨rfl⟩ μ hμ []`. Take `⟨β, hβ, hβe⟩` from `GlobalTheory.T.exists_test_function_lie_algebra_pullback_det E a α₀ hs hc`. Use `⟨β, hβ, fun f hf hpf => ?_⟩` and prove the remaining obligations. Take `⟨hF, h0⟩` from `(GlobalTheory.HCA.mem_solG (GlobalTheory.HCA.glH E a) b).1 (hsol f hf hpf)`. Establish `key` using `hα₀ ⟨_, hF⟩ h0 1`.

Simplify using `only [one_mul, List.foldr_nil] at key`. Use `set D : Lie E a → ℝ := fun x => |LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)| with hD`. Establish `hD0 : ∀ u : GL (Fin a) (Cinf E), D (toL u.val) ≠ 0` using `fun u => abs_ne_zero.2 (det_lmul_ne_zero u)`. Use `set Φ : Lie E a → ℂ := (invSet E a).indicator fun x => (D x : ℂ) * (β x * f x) with hΦ`. Establish `hΦc : ContinuousOn Φ (invSet E a)` using `((Complex.continuous_ofReal.comp continuous_absDet).continuousOn.mul (hβ.1.continuous.continuousOn.mul hf.continuousOn)).congr fun x hx => Set.indicator_of_mem hx _`.

Establish `hΦ0 : ∀ x ∉ invSet E a, Φ x = 0` using `fun x hx => Set.indicator_of_notMem hx _`. Establish `H` using `hint Φ hΦc hΦ0`. Establish `e1 : ∫ x, β x * f x ∂ν = ∫ x, (((D x)⁻¹ : ℝ) : ℂ) * Φ x ∂ν`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ invSet E a`.

Take `⟨u, hu⟩` from `hx`. Take `rfl : x = toL u.val` from `hu.symm`. Establish `h1 : ((D (toL u.val) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (hD0 u)`. Simplify using `only [hΦ, Set.indicator_of_mem (val_mem_invSet u)]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Establish `hb : β x = 0` using `image_eq_zero_of_notMem_tsupport fun h => hx (hβ.2.2 h)`. Simplify using `[hΦ0 x hx, hb]`. Establish `e2 : ∫ y, Φ (toL y.1.val) ∂μ = ∫ y, f (toL y.1.val) * α₀ y ∂μ`. Use `integral_congr_ae (ae_of_all _ fun y => ?_)` and prove the remaining obligations.

Establish `h1 : ((|LinearMap.det ((lmul (toL y.1.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)| : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (hD0 y.1)`. Use `beta_reduce`. Rewrite using `[hΦ, Set.indicator_of_mem (val_mem_invSet y.1), hβe y, hD]`. Simplify using `only`. Rewrite using `[Complex.ofReal_inv]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, ← H, e2]`. Conclude with `key`.
-/
theorem exists_test_reproducing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∀ p : Polynomial ℂ, p ≠ 0 → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) →
        ∫ y, α y * f y ∂ν = f (oneL E a) := by
  intro E _ _ _ a ν hν p hp
  obtain ⟨d, b, P, hP, hsol, -⟩ := GlobalTheory.T.laplacianPolynomialKernel_of_polynomial_laplacian E a p hp
  borelize ↥(GlobalTheory.HCA.glG E a)
  obtain ⟨μ, hμ, hint⟩ := GlobalTheory.T.exists_haar_GL_realPoints_density_det_inv E a ν hν
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  obtain ⟨α₀, hs, -, hc, hα₀⟩ := @GlobalTheory.T.exists_smooth_convolution_eq_derivative (Matrix (Fin a) (Fin a) (Cinf E)) _ _ _ _ (GlobalTheory.HCA.glG E a)
    (GlobalTheory.HCA.glL E a) (GlobalTheory.HCA.glH E a) d b P hP _ ⟨rfl⟩ μ hμ []
  obtain ⟨β, hβ, hβe⟩ := GlobalTheory.T.exists_test_function_lie_algebra_pullback_det E a α₀ hs hc
  refine ⟨β, hβ, fun f hf hpf => ?_⟩
  obtain ⟨hF, h0⟩ := (GlobalTheory.HCA.mem_solG (GlobalTheory.HCA.glH E a) b).1 (hsol f hf hpf)
  have key := hα₀ ⟨_, hF⟩ h0 1
  simp only [one_mul, List.foldr_nil] at key
  set D : Lie E a → ℝ := fun x => |LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)| with hD
  have hD0 : ∀ u : GL (Fin a) (Cinf E), D (toL u.val) ≠ 0 := fun u => abs_ne_zero.2 (det_lmul_ne_zero u)
  set Φ : Lie E a → ℂ := (invSet E a).indicator fun x => (D x : ℂ) * (β x * f x) with hΦ
  have hΦc : ContinuousOn Φ (invSet E a) :=
    ((Complex.continuous_ofReal.comp continuous_absDet).continuousOn.mul
      (hβ.1.continuous.continuousOn.mul hf.continuousOn)).congr fun x hx => Set.indicator_of_mem hx _
  have hΦ0 : ∀ x ∉ invSet E a, Φ x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have H := hint Φ hΦc hΦ0
  have e1 : ∫ x, β x * f x ∂ν = ∫ x, (((D x)⁻¹ : ℝ) : ℂ) * Φ x ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ invSet E a
    · obtain ⟨u, hu⟩ := hx
      obtain rfl : x = toL u.val := hu.symm
      have h1 : ((D (toL u.val) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hD0 u)
      simp only [hΦ, Set.indicator_of_mem (val_mem_invSet u)]
      push_cast
      field_simp
    · have hb : β x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hβ.2.2 h)
      simp [hΦ0 x hx, hb]
  have e2 : ∫ y, Φ (toL y.1.val) ∂μ = ∫ y, f (toL y.1.val) * α₀ y ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have h1 : ((|LinearMap.det ((lmul (toL y.1.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)| : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (hD0 y.1)
    beta_reduce
    rw [hΦ, Set.indicator_of_mem (val_mem_invSet y.1), hβe y, hD]
    dsimp only
    rw [Complex.ofReal_inv]
    field_simp
  rw [e1, ← H, e2]
  exact key
