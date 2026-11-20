import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff

namespace GlobalTheory.SympChange

/- English proof (translation)
Unfold `Sp.mat`. Rewrite using `[SymplecticGroup.det_eq_one γ.2]`. Evaluate the numerical expressions.
-/
theorem det_sq_eq_one {g : ℕ} (γ : Sp g) : γ.mat.det ^ 2 = 1 := by
  unfold Sp.mat
  rw [SymplecticGroup.det_eq_one γ.2]; norm_num

/- English proof (translation)
Use extensionality with `x i`. Simplify using `[Matrix.vecMul_transpose, Matrix.mulVec_transpose]`.
-/
theorem vecMulLinear_eq_toLin' {g : ℕ} (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) :
    Matrix.vecMulLinear A = Matrix.toLin' Aᵀ := by
  ext x i; simp [Matrix.vecMul_transpose, Matrix.mulVec_transpose]

/- English proof (translation)
Establish `hd : (LinearMap.toMatrix' (Matrix.vecMulLinear γ.mat)).det ^ 2 = 1`. Rewrite using `[vecMulLinear_eq_toLin', LinearMap.toMatrix'_toLin', Matrix.det_transpose]`. Conclude with `det_sq_eq_one γ`. Establish `hdet : LinearMap.det (Matrix.vecMulLinear γ.mat) ^ 2 = 1`. Rewrite using `[← LinearMap.det_toMatrix']`.

Conclude with `hd`. Establish `hne : LinearMap.det (Matrix.vecMulLinear γ.mat) ≠ 0`. Introduce `h0`. Rewrite `hdet` using `[h0]`. Simplify using `at hdet`.

Establish `habs : |(LinearMap.det (Matrix.vecMulLinear γ.mat))⁻¹| = 1`. Rewrite using `[abs_inv]`. Establish `: |LinearMap.det (Matrix.vecMulLinear γ.mat)| = 1`. Use `sq_abs (LinearMap.det (Matrix.vecMulLinear γ.mat))` as an intermediate fact. Rewrite `this` using `[hdet]`.

Establish `h0 : 0 ≤ |LinearMap.det (Matrix.vecMulLinear γ.mat)|` using `abs_nonneg _`. Use polynomial arithmetic with `[sq_nonneg (|LinearMap.det (Matrix.vecMulLinear γ.mat)| - 1)]`. Rewrite using `[this, inv_one]`. Use `⟨(Matrix.vecMulLinear γ.mat).continuous_of_finiteDimensional.measurable, ?_⟩` and prove the remaining obligations. Use `Real.map_linearMap_volume_pi_eq_smul_volume_pi hne` as an intermediate fact.

Rewrite `this` using `[habs, ENNReal.ofReal_one, one_smul]`. Conclude with `this`.
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
Unfold `Sp.mat`. Rewrite using `[SymplecticGroup.coe_inv']`. Conclude with `Matrix.nonsing_inv_mul _ (SymplecticGroup.symplectic_det γ.2)`.
-/
theorem inv_mul_mat {g : ℕ} (γ : Sp g) : (γ⁻¹).mat * γ.mat = 1 := by
  unfold Sp.mat
  rw [SymplecticGroup.coe_inv']
  exact Matrix.nonsing_inv_mul _ (SymplecticGroup.symplectic_det γ.2)

/- English proof (translation)
Establish `hmp` using `measurePreserving_vecMul γ⁻¹`. Set `e : Fl g ≃L[ℝ] Fl g` to `{ toLinearEquiv := { Matrix.vecMulLinear (γ⁻¹).mat with invFun := fun x => x ᵥ* γ.mat left_inv := fun x => by`. Simplify using `[Matrix.vecMul_vecMul, inv_mul_mat]`. Use `right_inv := fun x => by`. Establish `h : γ.mat * (γ⁻¹).mat = 1`.

Use `inv_mul_mat γ⁻¹` as an intermediate fact. Simplify using `using this`. Simplify using `[Matrix.vecMul_vecMul, h] }`. Use `continuous_toFun := (Matrix.vecMulLinear (γ⁻¹).mat).continuous_of_finiteDimensional`. Use `continuous_invFun := (Matrix.vecMulLinear γ.mat).continuous_of_finiteDimensional }`.

Establish `hemb : MeasurableEmbedding (fun x : Fl g => x ᵥ* (γ⁻¹).mat)` using `e.toHomeomorph.measurableEmbedding`. Conclude with `hmp.setIntegral_preimage_emb hemb φ D`.
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
