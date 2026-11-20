import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

namespace GlobalTheory.QhtUnip

/- English proof (translation)
Introduce `hdet`. Use `set P := incM F (basQ H) with hP`. Establish `hPu : IsUnit P.det`. Establish `: P.det = inclR (F` using `F) (E := E) (AF F) (basQ H).det := by`. Rewrite using `[hP, incM, RingHom.map_det]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hdet.map _`. Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hPu`. Establish `h2 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hPu`.

Establish `hmul : ∀ g h : UA σ J, mat (g * h) = mat g * mat h` using `fun g h => rfl`. Establish `hone : mat (1 : UA σ J) = 1` using `rfl`. Use `⟨fun g h => ?_, ?_, fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [crd]`. Rewrite using `[Matrix.submatrix_mul_equiv, hmul]`.

Use `congr 1`. Rewrite using `[← hP]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`. Simplify using `[Matrix.mul_assoc]`.

Use `_ = P⁻¹ * mat g * P * (P⁻¹ * mat h * P) := by simp only [Matrix.mul_assoc]`. Simplify using `only [crd]`. Rewrite using `[← hP, hone, Matrix.mul_one, h2, Matrix.submatrix_one_equiv]`. Simplify using `only [crd, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]`. Rewrite using `[← hP]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem crd_mul_one_mat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin (m + 2)) (Fin (m + 2)) E) (H : Plane E (m + 2) m) :
    IsUnit (basQ H).det → (∀ g h : UA σ J, crd H (g * h) = crd H g * crd H h) ∧ crd H (1 : UA σ J) = 1 ∧
      ∀ g : UA σ J, mat g = incM F (basQ H) * (crd H g).submatrix (ixE m) (ixE m) * (incM F (basQ H))⁻¹ := by
  intro hdet
  set P := incM F (basQ H) with hP
  have hPu : IsUnit P.det := by
    have : P.det = inclR (F := F) (E := E) (AF F) (basQ H).det := by
      rw [hP, incM, RingHom.map_det]; rfl
    rw [this]; exact hdet.map _
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have hmul : ∀ g h : UA σ J, mat (g * h) = mat g * mat h := fun g h => rfl
  have hone : mat (1 : UA σ J) = 1 := rfl
  refine ⟨fun g h => ?_, ?_, fun g => ?_⟩
  · simp only [crd]
    rw [Matrix.submatrix_mul_equiv, hmul]
    congr 1
    rw [← hP]
    calc P⁻¹ * (mat g * mat h) * P = P⁻¹ * mat g * (P * P⁻¹) * mat h * P := by
            rw [h1]; simp [Matrix.mul_assoc]
      _ = P⁻¹ * mat g * P * (P⁻¹ * mat h * P) := by simp only [Matrix.mul_assoc]
  · simp only [crd]
    rw [← hP, hone, Matrix.mul_one, h2, Matrix.submatrix_one_equiv]
  · simp only [crd, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
    rw [← hP]
    calc mat g = (P * P⁻¹) * mat g * (P * P⁻¹) := by rw [h1]; simp
      _ = P * (P⁻¹ * mat g * P) * P⁻¹ := by simp only [Matrix.mul_assoc]

end GlobalTheory.QhtUnip
