import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import GroundTheory.HeightsAndTheta.Theta.WeilNonarchProps
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup

open scoped NNReal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Simplify using `[Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two, Fin.succAbove]`.
-/
theorem det_three_points_eq_expansion (h : GL (Fin 2) F) :
    (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det
      = (h.val).det := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two, Fin.succAbove]

/- English proof (translation)
The claim follows from `((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero`.
-/
theorem det_ne (h : GL (Fin 2) F) : (h.val).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero

/- English proof (translation)
Establish `hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det ≠ 0`. Rewrite using `[det_three_points_eq_expansion]`. Conclude with `det_ne h`. Unfold `Ad3.K.GL2LocalData.em`. Rewrite using `[dif_pos hd]`.

Both sides reduce to the same expression.
-/
theorem em_val (h : GL (Fin 2) F) : (Ad3.K.GL2LocalData.em h).val =
    !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := by
  have hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [det_three_points_eq_expansion]
    exact det_ne h
  unfold Ad3.K.GL2LocalData.em
  rw [dif_pos hd]
  rfl

/- English proof (translation)
Rewrite using `[em_val]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [LFS.blk, cat3, Matrix.mul_apply, Fin.sum_univ_three]`.
-/
theorem blk_mul_em (h : GL (Fin 2) F) (x : Fin 2 → F) :
    LFS.blk x * (Ad3.K.GL2LocalData.em h).val = cat3 h.val x := by
  rw [em_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LFS.blk, cat3, Matrix.mul_apply, Fin.sum_univ_three]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[cat3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]`.
-/
theorem mul_concat_column (k A : Matrix (Fin 2) (Fin 2) F) (x : Fin 2 → F) :
    k * cat3 A x = cat3 (k * A) (k *ᵥ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cat3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]

/- English proof (translation)
Simplify using `only [mp, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]`. Conclude with `Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) s`.
-/
theorem mp_mul (a b : Fˣ) (s : ℂ) : mp (a * b) s = mp a s * mp b s := by
  simp only [mp, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) s

/- English proof (translation)
Use `modulus_ne_zero (K := F) a.ne_zero` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem modulus_unit_ne (a : Fˣ) : (((modulus (a : F) : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by
  have := modulus_ne_zero (K := F) a.ne_zero
  exact_mod_cast this

/- English proof (translation)
The claim follows from `Complex.cpow_add _ _ (modulus_unit_ne a)`.
-/
theorem mp_add (a : Fˣ) (s t : ℂ) : mp a (s + t) = mp a s * mp a t :=
  Complex.cpow_add _ _ (modulus_unit_ne a)

/- English proof (translation)
The claim follows from `Complex.cpow_one _`.
-/
theorem mp_one (a : Fˣ) : mp a 1 = ((modulus (a : F) : ℝ≥0) : ℝ) := Complex.cpow_one _

/- English proof (translation)
Establish `: ((GeneralLinearGroup.det (Ad3.K.GL2LocalData.em h) : Fˣ) : F) = ((GeneralLinearGroup.det h : Fˣ) : F)`. Simplify using `only [GeneralLinearGroup.val_det_apply]`. Rewrite using `[em_val, det_three_points_eq_expansion]`. Simplify using `only [mp, this]`.
-/
theorem mp_det_em (h : GL (Fin 2) F) (s : ℂ) :
    mp (GeneralLinearGroup.det (Ad3.K.GL2LocalData.em h)) s = mp (GeneralLinearGroup.det h) s := by
  have : ((GeneralLinearGroup.det (Ad3.K.GL2LocalData.em h) : Fˣ) : F) = ((GeneralLinearGroup.det h : Fˣ) : F) := by
    simp only [GeneralLinearGroup.val_det_apply]
    rw [em_val, det_three_points_eq_expansion]
  simp only [mp, this]

/- English proof (translation)
Establish `key` using `GroundTheory.Heights₂.Theta.integral_comp_mulVec (ψ := ψ) (det_ne k) (fun y => Φ (cat3 (k * h).val y) * (ψ (-((e2r k⁻¹) 0 * y 0 + (e2r k⁻¹) 1 * y 1)) : ℂ))`. Unfold `LFS.inn pFT`. Use `Eq.trans ?_ key` and prove the remaining obligations. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `hx : (k⁻¹ : GL (Fin 2) F).val *ᵥ (k.val *ᵥ x) = x`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]`. Simplify using the standard rewrite rules. Establish `h1 : -x 1 = -((e2r k⁻¹) 0 * (k.val *ᵥ x) 0 + (e2r k⁻¹) 1 * (k.val *ᵥ x) 1)`. Use `congrFun hx 1` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two]`.

Simplify using `only [e2r, Matrix.cons_val_zero, Matrix.cons_val_one]`. Conclude with `congrArg Neg.neg this.symm`. Establish `h2 : (k.val * LFS.blk x * (Ad3.K.GL2LocalData.em h).val) = cat3 (k * h).val (k.val *ᵥ x)`. Rewrite using `[Matrix.mul_assoc, blk_mul_em, mul_concat_column, Units.val_mul]`. Simplify using `only [h2, ← h1]`.
-/
theorem inn_em (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (k h : GL (Fin 2) F) :
    LFS.inn ψ Φ k (Ad3.K.GL2LocalData.em h) =
      ((((modulus (k.val).det)⁻¹ : ℝ≥0) : ℝ) : ℂ) * pFT ψ Φ (k * h).val (e2r k⁻¹) := by
  have key := GroundTheory.Heights₂.Theta.integral_comp_mulVec (ψ := ψ) (det_ne k)
    (fun y => Φ (cat3 (k * h).val y) *
      (ψ (-((e2r k⁻¹) 0 * y 0 + (e2r k⁻¹) 1 * y 1)) : ℂ))
  unfold LFS.inn pFT
  refine Eq.trans ?_ key
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : (k⁻¹ : GL (Fin 2) F).val *ᵥ (k.val *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
    simp
  have h1 : -x 1 = -((e2r k⁻¹) 0 * (k.val *ᵥ x) 0 + (e2r k⁻¹) 1 * (k.val *ᵥ x) 1) := by
    have := congrFun hx 1
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    simp only [e2r, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact congrArg Neg.neg this.symm
  have h2 : (k.val * LFS.blk x * (Ad3.K.GL2LocalData.em h).val) = cat3 (k * h).val (k.val *ᵥ x) := by
    rw [Matrix.mul_assoc, blk_mul_em, mul_concat_column, Units.val_mul]
  simp only [h2, ← h1]

end GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup

namespace GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup

open scoped NNReal

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ W₀ Φ hΦ h`. Use `haveI : (LFS.hG ψ).IsMulRightInvariant := by`. Unfold `LFS.hG`. Use `infer_instance`. Use `set f : GL (Fin 2) F → ℂ := fun g => pFT ψ Φ g.val (e2r (h * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) * W₀ (h * g⁻¹) with hf`.

Rewrite using `[← integral_mul_right_eq_self f h]`. Unfold `LFS.Wp`. Rewrite using `[mp_det_em]`. Establish `hpt : ∀ k : GL (Fin 2) F, W₀ k⁻¹ * mp (GeneralLinearGroup.det k) (3 / 2) * LFS.inn ψ Φ k (Ad3.K.GL2LocalData.em h) = (mp (GeneralLinearGroup.det h) (-(1 / 2))) * f (k * h)`. Introduce `k`.

Establish `e1 : h * (k * h)⁻¹ = k⁻¹` using `by group`. Establish `hm : ((modulus (k.val).det : ℝ≥0) : ℝ) = ((modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ≥0) : ℝ)`. Simplify using `only [GeneralLinearGroup.val_det_apply]`. Establish `hne` using `modulus_unit_ne (GeneralLinearGroup.det k)`. Establish `h3 : mp (GeneralLinearGroup.det k) (3 / 2) = mp (GeneralLinearGroup.det k) (1 / 2) * (((modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ≥0) : ℝ) : ℂ)`.

Rewrite using `[← mp_one, ← mp_add]`. Evaluate the numerical expressions. Establish `hh : mp (GeneralLinearGroup.det h) (-(1 / 2)) * mp (GeneralLinearGroup.det h) (1 / 2) = 1`. Rewrite using `[← mp_add, neg_add_cancel]`. Simplify using `[mp]`.

Rewrite using `[inn_em]`. Simplify using `only [hf, e1, map_mul, mp_mul]`. Rewrite using `[h3]`. Use `push_cast`. Rewrite using `[hm]`.

Establish `hmm` using `mul_inv_cancel₀ hne`. Take the linear combination `(W₀ k⁻¹ * mp (GeneralLinearGroup.det k) (1 / 2) * pFT ψ Φ (k * h).val (e2r k⁻¹)) * hmm - (pFT ψ Φ (k * h).val (e2r k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) * W₀ k⁻¹) * hh`. Simplify using `only [hpt]`. Rewrite using `[integral_const_mul, ← mul_assoc]`. Use `congr 1`.

Rewrite using `[← mp_add]`. Evaluate the numerical expressions.
-/
theorem main : Ad3.K.GL2LocalData.GodementSectionPartialFourier := by
  intro F _ _ _ _ _ _ ψ hψ W₀ Φ hΦ h
  haveI : (LFS.hG ψ).IsMulRightInvariant := by
    unfold LFS.hG
    infer_instance
  set f : GL (Fin 2) F → ℂ := fun g =>
    pFT ψ Φ g.val (e2r (h * g⁻¹)) * mp (GeneralLinearGroup.det g) (1 / 2) * W₀ (h * g⁻¹) with hf
  rw [← integral_mul_right_eq_self f h]
  unfold LFS.Wp
  rw [mp_det_em]
  have hpt : ∀ k : GL (Fin 2) F,
      W₀ k⁻¹ * mp (GeneralLinearGroup.det k) (3 / 2) * LFS.inn ψ Φ k (Ad3.K.GL2LocalData.em h) =
        (mp (GeneralLinearGroup.det h) (-(1 / 2))) * f (k * h) := by
    intro k
    have e1 : h * (k * h)⁻¹ = k⁻¹ := by group
    have hm : ((modulus (k.val).det : ℝ≥0) : ℝ) = ((modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ≥0) : ℝ) := by
      simp only [GeneralLinearGroup.val_det_apply]
    have hne := modulus_unit_ne (GeneralLinearGroup.det k)
    have h3 : mp (GeneralLinearGroup.det k) (3 / 2) =
        mp (GeneralLinearGroup.det k) (1 / 2) * (((modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ≥0) : ℝ) : ℂ) := by
      rw [← mp_one, ← mp_add]
      norm_num
    have hh : mp (GeneralLinearGroup.det h) (-(1 / 2)) * mp (GeneralLinearGroup.det h) (1 / 2) = 1 := by
      rw [← mp_add, neg_add_cancel]
      simp [mp]
    rw [inn_em]
    simp only [hf, e1, map_mul, mp_mul]
    rw [h3]
    push_cast
    rw [hm]
    have hmm := mul_inv_cancel₀ hne
    linear_combination (W₀ k⁻¹ * mp (GeneralLinearGroup.det k) (1 / 2) * pFT ψ Φ (k * h).val (e2r k⁻¹)) * hmm -
      (pFT ψ Φ (k * h).val (e2r k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) * W₀ k⁻¹) * hh
  simp only [hpt]
  rw [integral_const_mul, ← mul_assoc]
  congr 1
  rw [← mp_add]
  norm_num

end GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup
