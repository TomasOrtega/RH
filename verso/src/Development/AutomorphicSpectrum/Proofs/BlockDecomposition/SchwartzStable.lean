import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.StSmooth

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.GodementSectionC

open Ad3.K.LC

noncomputable def rightMulLin (h : GL (Fin 3) ℂ) :
    (M23 × (Fin 2 → ℂ)) ≃ₗ[ℝ] (M23 × (Fin 2 → ℂ)) where
  toFun v := (Matrix.of.symm (Matrix.of v.1 * (h : Matrix (Fin 3) (Fin 3) ℂ)), v.2)
  invFun v := (Matrix.of.symm (Matrix.of v.1 * ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)), v.2)
  map_add' v w := by
    refine Prod.ext ?_ rfl
    exact Matrix.add_mul (Matrix.of v.1) (Matrix.of w.1) (h : Matrix (Fin 3) (Fin 3) ℂ)
  map_smul' c v := by
    refine Prod.ext ?_ rfl
    exact Matrix.smul_mul c (Matrix.of v.1) (h : Matrix (Fin 3) (Fin 3) ℂ)
  left_inv v := by
    refine Prod.ext ?_ rfl
    change Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of v.1 * (h : Matrix (Fin 3) (Fin 3) ℂ))) *
      ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) = v.1
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, Equiv.symm_apply_apply]
  right_inv v := by
    refine Prod.ext ?_ rfl
    change Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of v.1 *
      ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ))) * (h : Matrix (Fin 3) (Fin 3) ℂ)) = v.1
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one, Equiv.symm_apply_apply]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem exists_rightTranslate (h : GL (Fin 3) ℂ) (Ψ : Sw) :
    ∃ Ψ' : Sw, ∀ (X : M23) (q : Fin 2 → ℂ),
      Ψ' (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ)), q) :=
  ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rightMulLin h).toContinuousLinearEquiv Ψ,
    fun _ _ => rfl⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem inn_smul (c : ℂ) (Ψ : Sw) (g : GL (Fin 3) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    inn (c • Ψ) g M t = c * inn Ψ g M t := by
  unfold inn
  rw [← integral_const_mul]
  congr 1
  funext p
  rw [SchwartzMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem inn_mul_right (Ψ Ψ₀ : Sw) (g h : GL (Fin 3) ℂ)
    (hΨ : ∀ (X : M23) (q : Fin 2 → ℂ),
      Ψ₀ (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ)), q))
    (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    inn Ψ (g * h) M t = inn Ψ₀ g M t := by
  unfold inn
  congr 1
  funext p
  rw [hΨ, Units.val_mul, ← Matrix.mul_assoc]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem stStable : StStable := by
  intro k _ Ψ h
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_rightTranslate h Ψ
  set c : ℂ := ((‖(h : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) with hc
  refine ⟨c • Ψ₀, ?_⟩
  funext g
  unfold sec
  simp only [inn_smul, inn_mul_right Ψ Ψ₀ g h hΨ₀]
  have hdet : ((‖((g * h : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) =
      ((‖(g : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) * c := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, mul_pow, Complex.ofReal_mul]
  have hin : ∀ y : M22, (∫ t : ℂ, c * inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t) =
      c * ∫ t : ℂ, inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t := by
    intro y
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  have hout : (∫ y : M22, (c * ∫ t : ℂ, inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t) *
        ph (-(2 * (k : ℤ) - 2)) (Matrix.of y).det *
        ((‖(Matrix.of y).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ)) =
      c * ∫ y : M22, (∫ t : ℂ, inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t) *
        ph (-(2 * (k : ℤ) - 2)) (Matrix.of y).det *
        ((‖(Matrix.of y).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  simp only [hin]
  rw [hdet, hout]
  ring

end GlobalTheory.CompanionTheory.GodementSectionC
