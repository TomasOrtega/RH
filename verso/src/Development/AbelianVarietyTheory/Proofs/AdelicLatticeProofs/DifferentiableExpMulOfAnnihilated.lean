import Mathlib
open Matrix

namespace GlobalTheory

open Matrix in

/- English proof (translation)
Introduce `g Hm _ f hfd hann`. Set `B0 : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℂ` to `LinearMap.mk₂ ℝ (fun u v => u ⬝ᵥ Hm.mulVec (star v)) (fun u₁ u₂ v => by simp [add_dotProduct]) (fun r u v => by simp [smul_dotProduct]) (fun u v₁ v₂ => by simp [star_add, Matrix.mulVec_add, dotProduct_add]) (fun r u v => by simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])`. Set `B : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) →L[ℝ] ℂ` to `LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B0)`. Establish `hB : ∀ u v, B u v = u ⬝ᵥ Hm.mulVec (star v)` using `fun u v => rfl`. Establish `hQ : ∀ w : Fin g → ℂ, HasFDerivAt (fun w : Fin g → ℂ => w ⬝ᵥ Hm.mulVec (star w)) (B.precompR _ w (ContinuousLinearMap.id ℝ _) + B.precompL _ (ContinuousLinearMap.id ℝ _) w) w` using `fun w => B.hasFDerivAt_of_bilinear (hasFDerivAt_id w) (hasFDerivAt_id w)`.

Introduce `w`. Establish `hF : HasFDerivAt (fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w) _ w` using `(((hQ w).const_mul ((Real.pi : ℂ) / 2)).cexp).mul (hfd w).hasFDerivAt`. Use `(differentiableAt_iff_restrictScalars ℝ hF.differentiableAt).2 ?_` and prove the remaining obligations. Rewrite using `[hF.fderiv]`. Use `set e := Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) with he`.

Use `set T := e • fderiv ℝ f w + f w • (e • (((Real.pi : ℂ) / 2) • (B.precompR _ w (ContinuousLinearMap.id ℝ _) + B.precompL _ (ContinuousLinearMap.id ℝ _) w))) with hTdef`. Establish `hT : ∀ z, T z = e * fderiv ℝ f w z + f w * (e * ((Real.pi : ℂ) / 2 * (w ⬝ᵥ Hm.mulVec (star z) + z ⬝ᵥ Hm.mulVec (star w))))`. Introduce `z`. Use `clear hann hQ hF hTdef`. Simplify using `only [T, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hB, smul_eq_mul]`.

Establish `key : ∀ z, T (Complex.I • z) = Complex.I • T z`. Introduce `z`. Establish `h1` using `hann w z`. Establish `hs1 : w ⬝ᵥ Hm.mulVec (star (Complex.I • z)) = -Complex.I * (w ⬝ᵥ Hm.mulVec (star z))`. Simplify using `[Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul]`.

Establish `hs2 : (Complex.I • z) ⬝ᵥ Hm.mulVec (star w) = Complex.I * (z ⬝ᵥ Hm.mulVec (star w))`. Simplify using `[smul_dotProduct]`. Rewrite `h1` using `[hs1]`. Rewrite using `[hT, hT, hs1, hs2, smul_eq_mul]`. Use `set b := w ⬝ᵥ Hm.mulVec (star z)`.

Establish `him : (-Complex.I * b).im = -b.re` using `by simp`. Rewrite `h1` using `[him]`. Establish `hb : b = b.re + b.im * Complex.I` using `(Complex.re_add_im b).symm`. Move the coercions through the operations in `at h1`. Take the linear combination `(-Complex.I * e) * h1 + (-Complex.I * e * Real.pi * f w) * hb + (e * fderiv ℝ f w (Complex.I • z) - Real.pi * Complex.I * e * b.re * f w) * Complex.I_sq`.

Set `L : (Fin g → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := T map_add' := T.map_add map_smul' := fun c z => by`. Establish `hc : c • z = c.re • z + c.im • (Complex.I • z)`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]`. Use `conv_lhs => rw [← Complex.re_add_im c]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, T.map_add, T.map_smul, T.map_smul, key, RingHom.id_apply]`. Simplify using `only [Complex.real_smul, smul_eq_mul]`. Use `conv_rhs => rw [← Complex.re_add_im c]`. Use `ring }`.

Conclude with `⟨LinearMap.toContinuousLinearMap L, ContinuousLinearMap.ext fun z => rfl⟩`.
-/
theorem _root_.GlobalTheory.differentiable_exp_mul_of_annihilated :
    ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℝ f → (∀ w z : Fin g → ℂ, (fderiv ℝ f w z + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star z)).im : ℂ) * f w) + Complex.I * (fderiv ℝ f w (Complex.I • z) + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star (Complex.I • z))).im : ℂ) * f w) = 0) → Differentiable ℂ fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w := by
  intro g Hm _ f hfd hann
  let B0 : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℂ :=
    LinearMap.mk₂ ℝ (fun u v => u ⬝ᵥ Hm.mulVec (star v))
      (fun u₁ u₂ v => by simp [add_dotProduct])
      (fun r u v => by simp [smul_dotProduct])
      (fun u v₁ v₂ => by simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (fun r u v => by simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  let B : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B0)
  have hB : ∀ u v, B u v = u ⬝ᵥ Hm.mulVec (star v) := fun u v => rfl
  have hQ : ∀ w : Fin g → ℂ, HasFDerivAt (fun w : Fin g → ℂ => w ⬝ᵥ Hm.mulVec (star w))
      (B.precompR _ w (ContinuousLinearMap.id ℝ _) + B.precompL _ (ContinuousLinearMap.id ℝ _) w) w :=
    fun w => B.hasFDerivAt_of_bilinear (hasFDerivAt_id w) (hasFDerivAt_id w)
  intro w
  have hF : HasFDerivAt (fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w) _ w :=
    (((hQ w).const_mul ((Real.pi : ℂ) / 2)).cexp).mul (hfd w).hasFDerivAt
  refine (differentiableAt_iff_restrictScalars ℝ hF.differentiableAt).2 ?_
  rw [hF.fderiv]
  set e := Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) with he
  set T := e • fderiv ℝ f w + f w • (e • (((Real.pi : ℂ) / 2) •
    (B.precompR _ w (ContinuousLinearMap.id ℝ _) + B.precompL _ (ContinuousLinearMap.id ℝ _) w)))
    with hTdef
  have hT : ∀ z, T z = e * fderiv ℝ f w z + f w * (e * ((Real.pi : ℂ) / 2 *
      (w ⬝ᵥ Hm.mulVec (star z) + z ⬝ᵥ Hm.mulVec (star w)))) := by
    intro z
    clear hann hQ hF hTdef
    simp only [T, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, hB, smul_eq_mul]
  have key : ∀ z, T (Complex.I • z) = Complex.I • T z := by
    intro z
    have h1 := hann w z
    have hs1 : w ⬝ᵥ Hm.mulVec (star (Complex.I • z)) = -Complex.I * (w ⬝ᵥ Hm.mulVec (star z)) := by
      simp [Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul]
    have hs2 : (Complex.I • z) ⬝ᵥ Hm.mulVec (star w) = Complex.I * (z ⬝ᵥ Hm.mulVec (star w)) := by
      simp [smul_dotProduct]
    rw [hs1] at h1
    rw [hT, hT, hs1, hs2, smul_eq_mul]
    set b := w ⬝ᵥ Hm.mulVec (star z)
    have him : (-Complex.I * b).im = -b.re := by simp
    rw [him] at h1
    have hb : b = b.re + b.im * Complex.I := (Complex.re_add_im b).symm
    push_cast at h1
    linear_combination (-Complex.I * e) * h1 + (-Complex.I * e * Real.pi * f w) * hb +
      (e * fderiv ℝ f w (Complex.I • z) - Real.pi * Complex.I * e * b.re * f w) * Complex.I_sq
  let L : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun c z => by
        have hc : c • z = c.re • z + c.im • (Complex.I • z) := by
          ext i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im c]
          ring
        rw [hc, T.map_add, T.map_smul, T.map_smul, key, RingHom.id_apply]
        simp only [Complex.real_smul, smul_eq_mul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring }
  exact ⟨LinearMap.toContinuousLinearMap L, ContinuousLinearMap.ext fun z => rfl⟩

end GlobalTheory
