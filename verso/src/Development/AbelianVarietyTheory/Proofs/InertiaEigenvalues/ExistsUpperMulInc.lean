import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsOfValILeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp

/- English proof (translation)
Introduce `g hg n h`. Establish `hdet : ((h⁻¹ : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero`. Take `⟨k, U, hk, hU, -, hA⟩` from `Formalism.L2.Pj.iwasawa (V := ℤ_[g]) _ hdet`. Establish `hUdet : IsUnit U.det`. Rewrite `hdet` using `[hA, Matrix.det_mul]`.

Conclude with `isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)`. Set `K : GL (Fin n) ℤ_[g]` to `((Matrix.isUnit_iff_isUnit_det k).mpr hk).unit`. Establish `hinc : ((inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) = k.map (algebraMap ℤ_[g] ℚ_[g])` using `rfl`. Use `⟨h * inc g n K, K⁻¹, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`.

Establish `e1 : ((h * inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) = U⁻¹`. Rewrite using `[Units.val_mul, hinc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv U hUdet, Matrix.mul_one]`. Use `_ = U⁻¹ := by rw [← hA, Units.mul_inv, Matrix.one_mul]`.

Rewrite using `[e1]`. Use `haveI := Matrix.invertibleOfIsUnitDet U hUdet`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hU hij`. Rewrite using `[map_inv, mul_inv_cancel_right]`.
-/
theorem exists_upper_mul_inc : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (h : GL (Fin n) ℚ_[g]), ∃ (p : GL (Fin n) ℚ_[g]) (k : GL (Fin n) ℤ_[g]), (∀ i j : Fin n, j < i → (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j = 0) ∧ h = p * inc g n k := by
  intro g hg n h
  have hdet : ((h⁻¹ : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero
  obtain ⟨k, U, hk, hU, -, hA⟩ := Formalism.L2.Pj.iwasawa (V := ℤ_[g]) _ hdet

  have hUdet : IsUnit U.det := by
    rw [hA, Matrix.det_mul] at hdet
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  let K : GL (Fin n) ℤ_[g] := ((Matrix.isUnit_iff_isUnit_det k).mpr hk).unit
  have hinc : ((inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) =
      k.map (algebraMap ℤ_[g] ℚ_[g]) := rfl
  refine ⟨h * inc g n K, K⁻¹, ?_, ?_⟩
  · intro i j hij
    have e1 : ((h * inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) = U⁻¹ := by
      rw [Units.val_mul, hinc]
      calc (h : Matrix (Fin n) (Fin n) ℚ_[g]) * k.map (algebraMap ℤ_[g] ℚ_[g])
          = (h : Matrix (Fin n) (Fin n) ℚ_[g]) * (k.map (algebraMap ℤ_[g] ℚ_[g]) * U) * U⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv U hUdet, Matrix.mul_one]
        _ = U⁻¹ := by rw [← hA, Units.mul_inv, Matrix.one_mul]
    rw [e1]
    haveI := Matrix.invertibleOfIsUnitDet U hUdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU hij
  · rw [map_inv, mul_inv_cancel_right]

end GlobalTheory.GLp
