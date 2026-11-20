import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralAddRightMulChar

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhittakerPsi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem det_left_unipotent_mul (x : F) (g : GL (Fin 2) F) :
    GeneralLinearGroup.det (uni2 x * g) = GeneralLinearGroup.det g := by
  rw [map_mul]
  have : GeneralLinearGroup.det (uni2 x) = 1 := by
    ext
    simp [uni2, GeneralLinearGroup.det, Matrix.det_fin_two]
  rw [this, one_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem row_vector_mul_upper_unipotent (h y x : F) (g : GL (Fin 2) F) :
    ![h, h * y] ᵥ* ((uni2 x * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ![h, h * (y + x)] ᵥ* (g : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  exact GlobalTheory.CompanionTheory.PsiShift.vecMul_unipotent h y x

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem whittaker_upper_unipotent_equivariance (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (x : F)
    (g : GL (Fin 2) F) :
    W2 ψ μ₁ μ₂ φ (uni2 x * g) = (ψ x : ℂ) * W2 ψ μ₁ μ₂ φ g := by
  have inner : ∀ h : Fˣ,
      (∫ y, φ (![(h : F), h * y] ᵥ* ((uni2 x * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-y) : ℂ) ∂selfDualMeasure ψ) =
      (ψ x : ℂ) * ∫ y, φ (![(h : F), h * y] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-y) : ℂ) ∂selfDualMeasure ψ := by
    intro h
    simp only [row_vector_mul_upper_unipotent]
    exact GlobalTheory.CompanionTheory.PsiShift.integral_add_right_mul_char (selfDualMeasure ψ) ψ
      (fun y => φ (![(h : F), h * y] ᵥ* (g : Matrix (Fin 2) (Fin 2) F))) x
  unfold W2
  rw [det_left_unipotent_mul]
  simp only [inner]
  have e : ∀ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      ((ψ x : ℂ) * ∫ y, φ (![(h : F), h * y] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-y) : ℂ) ∂selfDualMeasure ψ) =
      (ψ x : ℂ) * ((((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      ∫ y, φ (![(h : F), h * y] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) *
        (ψ (-y) : ℂ) ∂selfDualMeasure ψ) := fun h => by ring
  simp only [e]
  rw [integral_const_mul]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem sPsi : SPsi := by
  intro F _ _ _ _ _ _ ψ _ μ₁ μ₂ _ _ φ _ x g
  exact whittaker_upper_unipotent_equivariance ψ μ₁ μ₂ φ x g

end GlobalTheory.CompanionTheory.WhittakerPsi
