import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff

namespace GlobalTheory.SympChange

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem det_sq_eq_one {g : ℕ} (γ : Sp g) : γ.mat.det ^ 2 = 1 := by
  unfold Sp.mat
  rw [SymplecticGroup.det_eq_one γ.2]; norm_num

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem vecMulLinear_eq_toLin' {g : ℕ} (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) :
    Matrix.vecMulLinear A = Matrix.toLin' Aᵀ := by
  ext x i; simp [Matrix.vecMul_transpose, Matrix.mulVec_transpose]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem measurePreserving_vecMul {g : ℕ} (γ : Sp g) :
    MeasurePreserving (fun x : Fl g => x ᵥ* γ.mat) volume volume := by
  have hd : (LinearMap.toMatrix' (Matrix.vecMulLinear γ.mat)).det ^ 2 = 1 := by
    rw [vecMulLinear_eq_toLin', LinearMap.toMatrix'_toLin', Matrix.det_transpose]
    exact det_sq_eq_one γ
  have hdet : LinearMap.det (Matrix.vecMulLinear γ.mat) ^ 2 = 1 := by
    rw [← LinearMap.det_toMatrix']; exact hd
  have hne : LinearMap.det (Matrix.vecMulLinear γ.mat) ≠ 0 := by
    intro h0; rw [h0] at hdet; simp at hdet
  have habs : |(LinearMap.det (Matrix.vecMulLinear γ.mat))⁻¹| = 1 := by
    rw [abs_inv]
    have : |LinearMap.det (Matrix.vecMulLinear γ.mat)| = 1 := by
      have := sq_abs (LinearMap.det (Matrix.vecMulLinear γ.mat))
      rw [hdet] at this
      have h0 : 0 ≤ |LinearMap.det (Matrix.vecMulLinear γ.mat)| := abs_nonneg _
      nlinarith [sq_nonneg (|LinearMap.det (Matrix.vecMulLinear γ.mat)| - 1)]
    rw [this, inv_one]
  refine ⟨(Matrix.vecMulLinear γ.mat).continuous_of_finiteDimensional.measurable, ?_⟩
  have := Real.map_linearMap_volume_pi_eq_smul_volume_pi hne
  rw [habs, ENNReal.ofReal_one, one_smul] at this
  exact this

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem inv_mul_mat {g : ℕ} (γ : Sp g) : (γ⁻¹).mat * γ.mat = 1 := by
  unfold Sp.mat
  rw [SymplecticGroup.coe_inv']
  exact Matrix.nonsing_inv_mul _ (SymplecticGroup.symplectic_det γ.2)

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem setIntegral_vecMul_inv {g : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (γ : Sp g) (D : Set (Fl g)) (φ : Fl g → F) :
    ∫ x in (fun x : Fl g => x ᵥ* (γ⁻¹).mat) ⁻¹' D, φ (x ᵥ* (γ⁻¹).mat) = ∫ x in D, φ x := by
  have hmp := measurePreserving_vecMul γ⁻¹
  let e : Fl g ≃L[ℝ] Fl g :=
    { toLinearEquiv :=
        { Matrix.vecMulLinear (γ⁻¹).mat with
          invFun := fun x => x ᵥ* γ.mat
          left_inv := fun x => by
            simp [Matrix.vecMul_vecMul, inv_mul_mat]
          right_inv := fun x => by
            have h : γ.mat * (γ⁻¹).mat = 1 := by
              have := inv_mul_mat γ⁻¹; simpa using this
            simp [Matrix.vecMul_vecMul, h] }
      continuous_toFun := (Matrix.vecMulLinear (γ⁻¹).mat).continuous_of_finiteDimensional
      continuous_invFun := (Matrix.vecMulLinear γ.mat).continuous_of_finiteDimensional }
  have hemb : MeasurableEmbedding (fun x : Fl g => x ᵥ* (γ⁻¹).mat) :=
    e.toHomeomorph.measurableEmbedding
  exact hmp.setIntegral_preimage_emb hemb φ D

end GlobalTheory.SympChange
