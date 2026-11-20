import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFCen

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem mp_mul (x y : Fˣ) (s : ℂ) : mp (x * y) s = mp x s * mp y s := by
  unfold mp
  rw [Units.val_mul, GroundTheory.LocalField.modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mp_scale (a : Fˣ) : mp (a * a * a) 1 * mp (a⁻¹ * a⁻¹) (3 / 2) = 1 := by
  have ht : 0 < (modulus (a : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos a.ne_zero
  unfold mp
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, GroundTheory.LocalField.modulus_mul,
    GroundTheory.LocalField.modulus_inv, NNReal.coe_mul, NNReal.coe_inv]
  generalize (modulus (a : F) : ℝ) = t at ht
  have e : ((t⁻¹ * t⁻¹ : ℝ) : ℂ) ^ (3 / 2 : ℂ) = (((t⁻¹ * t⁻¹) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have e2 : (t⁻¹ * t⁻¹) ^ (3 / 2 : ℝ) * (t * t * t) = 1 := by
    have : t⁻¹ * t⁻¹ = t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg ht.le, Real.rpow_two]
      field_simp
    rw [this, ← Real.rpow_mul ht.le]
    have : t * t * t = t ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [this, ← Real.rpow_add ht]
    norm_num
  push_cast at e ⊢
  rw [Complex.cpow_one, e]
  have := congrArg (fun r : ℝ => (r : ℂ)) e2
  push_cast at this
  rw [mul_comm]
  exact this

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem blk_scalar (a : Fˣ) (x : Fin 2 → F) :
    blk x * ((dg a a a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((dg2 a a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * blk x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, dg, dg2, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, mul_comm]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem inn_scalar (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h : GL (Fin 2) F)
    (g : GL (Fin 3) F) (a : Fˣ) : inn ψ Φ h (dg a a a * g) = inn ψ Φ (h * dg2 a a) g := by
  unfold inn
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have : (h : Matrix (Fin 2) (Fin 2) F) * blk x * ((dg a a a * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((h * dg2 a a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * blk x * (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ (blk x), blk_scalar,
      Matrix.mul_assoc _ _ (blk x)]
  simp only [this]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem det_dg (a : Fˣ) : GeneralLinearGroup.det (dg a a a) = a * a * a := by
  ext
  simp [dg, Matrix.det_fin_three]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem det_diagonal_two (a : Fˣ) : GeneralLinearGroup.det (dg2 a a) = a * a := by
  ext
  simp [dg2, Matrix.det_fin_two]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem scenW : Ad3.LFS.SCenW := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hyp a g
  obtain ⟨-, -, ⟨V', hV, hW⟩, -⟩ := hyp
  have hc : ∀ g, W' (dg2 a a * g) = W' g := fun g => by
    rw [hV.cen W' hW a g]
    simp
  have hI : ∫ h, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h (dg a a a * g) ∂hG ψ =
      mp (a⁻¹ * a⁻¹) (3 / 2) * ∫ h, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h g ∂hG ψ := by
    rw [← integral_const_mul]
    haveI : (hG ψ).IsMulRightInvariant := by
      unfold hG
      infer_instance
    rw [← integral_mul_right_eq_self (μ := hG ψ)
      (fun h => mp (a⁻¹ * a⁻¹) (3 / 2) * (W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h g)) (dg2 a a)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    have hw : W' (h * dg2 a a)⁻¹ = W' h⁻¹ := by
      rw [← hc (h * dg2 a a)⁻¹, _root_.mul_inv_rev, mul_inv_cancel_left]
    have hm : mp (a⁻¹ * a⁻¹) (3 / 2) * mp (GeneralLinearGroup.det (h * dg2 a a)) (3 / 2) =
        mp (GeneralLinearGroup.det h) (3 / 2) := by
      rw [map_mul, det_diagonal_two, ← mp_mul]
      congr 1
      rw [mul_comm, mul_assoc, show a * a * (a⁻¹ * a⁻¹) = (1 : Fˣ) by group, mul_one]
    simp only
    rw [inn_scalar, hw, ← hm]
    ring
  unfold Wp
  rw [hI, map_mul, det_dg, mp_mul, ← mul_assoc, mul_right_comm (mp _ 1), mp_scale, one_mul]

end GlobalTheory.CompanionTheory.LFCen
