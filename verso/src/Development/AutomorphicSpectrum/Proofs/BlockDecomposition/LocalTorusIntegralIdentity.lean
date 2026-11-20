import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFGTorus

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Unfold `mp`. Rewrite using `[Units.val_mul, GroundTheory.LocalField.modulus_mul, NNReal.coe_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]`.
-/
theorem mp_mul (x y : Fˣ) (s : ℂ) : mp (x * y) s = mp x s * mp y s := by
  unfold mp
  rw [Units.val_mul, GroundTheory.LocalField.modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

/- English proof (translation)
Unfold `mp`. Use `Complex.cpow_add _ _ ?_` and prove the remaining obligations. Use `GroundTheory.LocalField.modulus_ne_zero x.ne_zero` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem mp_add (x : Fˣ) (a b : ℂ) : mp x (a + b) = mp x a * mp x b := by
  unfold mp
  refine Complex.cpow_add _ _ ?_
  have := GroundTheory.LocalField.modulus_ne_zero x.ne_zero
  exact_mod_cast this

/- English proof (translation)
Simplify using `[mp]`.
-/
theorem mp_zero (x : Fˣ) : mp x 0 = 1 := by simp [mp]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[blk, col3, dg, dg2, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]`.
-/
theorem blk_dg (h : Matrix (Fin 2) (Fin 2) F) (t₁ t₂ : Fˣ) (x : Fin 2 → F) :
    h * blk x * ((dg t₁ t₂ 1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      col3 (h * ((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) (h *ᵥ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, col3, dg, dg2, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]

/- English proof (translation)
Establish `key` using `GlobalTheory.WeilM.integral_comp_mulVec (selfDualMeasure ψ) h f`. Establish `hm : ((distribHaarChar F (GeneralLinearGroup.det h) : ℝ) : ℂ) = mp (GeneralLinearGroup.det h) 1`. Rewrite using `[distribHaarChar_eq_modulus]`. Simplify using `[mp]`. Rewrite `key` using `[hm]`.

Unfold `vol2`. Rewrite using `[← key, ← mul_assoc, ← mp_add]`. Simplify using `[mp_zero]`.
-/
theorem integral_mulVec (ψ : AddChar F Circle) (h : GL (Fin 2) F) (f : (Fin 2 → F) → ℂ) :
    ∫ x, f ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ x) ∂vol2 ψ =
      mp (GeneralLinearGroup.det h) (-1) * ∫ y, f y ∂vol2 ψ := by
  have key := GlobalTheory.WeilM.integral_comp_mulVec (selfDualMeasure ψ) h f
  have hm : ((distribHaarChar F (GeneralLinearGroup.det h) : ℝ) : ℂ) = mp (GeneralLinearGroup.det h) 1 := by
    rw [distribHaarChar_eq_modulus]; simp [mp]
  rw [hm] at key
  unfold vol2
  rw [← key, ← mul_assoc, ← mp_add]
  simp [mp_zero]

/- English proof (translation)
Unfold `pft`. Rewrite using `[← integral_mulVec ψ h]`. Unfold `inn`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `hx : ∑ j, (t₂ : F) * (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j * ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ x) j = x 1`.

Establish `e : (t₂ : F) • (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 = (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) 1`. Use extensionality with `j`. Simplify using `[dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e2 : (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) * (h : Matrix (Fin 2) (Fin 2) F) = 1`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`.

Simplify using the standard rewrite rules. Establish `e3 : ∀ j, (t₂ : F) * (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j = (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) 1 j` using `fun j => congrFun e j`. Simplify using `only [e3]`. Establish `e4` using `congrFun (Matrix.mulVec_mulVec x (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) (h : Matrix (Fin 2) (Fin 2) F)) 1`. Rewrite `e4` using `[e2, Matrix.one_mulVec]`.

Conclude with `e4`. Establish `hb` using `blk_dg (h : Matrix (Fin 2) (Fin 2) F) t₁ t₂ x`. Rewrite `hb` using `[← Units.val_mul]`. Use `beta_reduce`. Rewrite using `[hb, hx]`.
-/
theorem inn_dg (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h : GL (Fin 2) F) (t₁ t₂ : Fˣ) :
    inn ψ Φ h (dg t₁ t₂ 1) = mp (GeneralLinearGroup.det h) (-1) *
      pft ψ Φ ((h * dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        (fun j => (t₂ : F) * (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) := by
  unfold pft
  rw [← integral_mulVec ψ h]
  unfold inn
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : ∑ j, (t₂ : F) * (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j *
      ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ x) j = x 1 := by
    have e : (t₂ : F) • (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 =
        (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) 1 := by
      ext j
      simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
    have e2 : (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) *
        (h : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, ← Units.val_mul]
      simp
    have e3 : ∀ j, (t₂ : F) * (((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j =
        (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) 1 j :=
      fun j => congrFun e j
    simp only [e3]
    have e4 := congrFun (Matrix.mulVec_mulVec x (((dg2 t₁ t₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((h * dg2 t₁ t₂)⁻¹ : GL (Fin 2) F).val) (h : Matrix (Fin 2) (Fin 2) F)) 1
    rw [e2, Matrix.one_mulVec] at e4
    exact e4
  have hb := blk_dg (h : Matrix (Fin 2) (Fin 2) F) t₁ t₂ x
  rw [← Units.val_mul] at hb
  beta_reduce
  rw [hb, hx]

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ ν W' Φ _ t₁ t₂`. Establish `hdet : GeneralLinearGroup.det (dg t₁ t₂ 1) = t₁ * t₂`. Use `ext`. Simplify using `[dg, Matrix.det_fin_three]`. Establish `hdet2 : GeneralLinearGroup.det (dg2 t₁ t₂) = t₁ * t₂`.

Use `ext`. Simplify using `[dg2, Matrix.det_fin_two]`. Unfold `Wp`. Rewrite using `[hdet]`. Use `set G : GL (Fin 2) F → ℂ := fun k => W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) * pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) with hGd`.

Establish `alg : ∀ w a b p c d : ℂ, c * d = 1 → w * a * (b * p) = c * (w * (a * b * d) * p)`. Introduce `w a b p c d hcd`. Take the linear combination `(-(w * a * b * p)) * hcd`. Establish `hpt : ∀ h : GL (Fin 2) F, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h (dg t₁ t₂ 1) = mp (t₁ * t₂) (-(1 / 2)) * G (h * dg2 t₁ t₂)`. Introduce `h`.

Establish `hw : dg2 t₁ t₂ * (h * dg2 t₁ t₂)⁻¹ = h⁻¹` using `by group`. Establish `hm : mp (GeneralLinearGroup.det (h * dg2 t₁ t₂)) (1 / 2) = mp (GeneralLinearGroup.det h) (3 / 2) * mp (GeneralLinearGroup.det h) (-1) * mp (t₁ * t₂) (1 / 2)`. Rewrite using `[map_mul, hdet2, mp_mul, ← mp_add]`. Evaluate the numerical expressions. Establish `hc : mp (t₁ * t₂) (-(1 / 2)) * mp (t₁ * t₂) (1 / 2) = 1`.

Rewrite using `[← mp_add]`. Simplify using `[mp_zero]`. Rewrite using `[inn_dg, hGd]`. Use `beta_reduce`. Rewrite using `[hw, hm]`.

Conclude with `alg _ _ _ _ _ _ hc`. Use `haveI : (hG ψ).IsMulRightInvariant := by`. Unfold `hG`. Use `infer_instance`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, integral_mul_right_eq_self (μ := hG ψ) G (dg2 t₁ t₂), ← mul_assoc, ← mp_add]`.

Evaluate the numerical expressions.
-/
theorem gtorus : Ad3.LFS.GTorus := by
  intro F _ _ _ _ _ _ ψ ν W' Φ _ t₁ t₂
  have hdet : GeneralLinearGroup.det (dg t₁ t₂ 1) = t₁ * t₂ := by
    ext
    simp [dg, Matrix.det_fin_three]
  have hdet2 : GeneralLinearGroup.det (dg2 t₁ t₂) = t₁ * t₂ := by
    ext
    simp [dg2, Matrix.det_fin_two]
  unfold Wp
  rw [hdet]
  set G : GL (Fin 2) F → ℂ := fun k => W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
      pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) with hGd
  have alg : ∀ w a b p c d : ℂ, c * d = 1 → w * a * (b * p) = c * (w * (a * b * d) * p) := by
    intro w a b p c d hcd
    linear_combination (-(w * a * b * p)) * hcd
  have hpt : ∀ h : GL (Fin 2) F, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h (dg t₁ t₂ 1) =
      mp (t₁ * t₂) (-(1 / 2)) * G (h * dg2 t₁ t₂) := by
    intro h
    have hw : dg2 t₁ t₂ * (h * dg2 t₁ t₂)⁻¹ = h⁻¹ := by group
    have hm : mp (GeneralLinearGroup.det (h * dg2 t₁ t₂)) (1 / 2) =
        mp (GeneralLinearGroup.det h) (3 / 2) * mp (GeneralLinearGroup.det h) (-1) * mp (t₁ * t₂) (1 / 2) := by
      rw [map_mul, hdet2, mp_mul, ← mp_add]
      norm_num
    have hc : mp (t₁ * t₂) (-(1 / 2)) * mp (t₁ * t₂) (1 / 2) = 1 := by
      rw [← mp_add]
      simp [mp_zero]
    rw [inn_dg, hGd]
    beta_reduce
    rw [hw, hm]
    exact alg _ _ _ _ _ _ hc
  haveI : (hG ψ).IsMulRightInvariant := by
    unfold hG
    infer_instance
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_mul_right_eq_self (μ := hG ψ) G (dg2 t₁ t₂), ← mul_assoc, ← mp_add]
  norm_num

end GlobalTheory.CompanionTheory.LFGTorus
