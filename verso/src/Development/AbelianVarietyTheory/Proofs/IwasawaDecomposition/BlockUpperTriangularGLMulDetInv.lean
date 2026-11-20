import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.HQStepBlocks

variable {F : Type} [Field F] {r c : ℕ}

/- English proof (translation)
Apply the tactic sequence `ext (i|i) (j|j) <;> simp [bAA, bAD, bDA, bDD]`.
-/
theorem submatrix_eq_fromBlocks (x : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    x.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (bAA x) (bAD x) (bDA x) (bDD x) := by
  ext (i|i) (j|j) <;> simp [bAA, bAD, bDA, bDD]

/- English proof (translation)
Rewrite using `[Matrix.submatrix_mul_equiv]`.
-/
theorem submatrix_mul' (x y : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    (x * y).submatrix finSumFinEquiv finSumFinEquiv =
      x.submatrix finSumFinEquiv finSumFinEquiv * y.submatrix finSumFinEquiv finSumFinEquiv := by
  rw [Matrix.submatrix_mul_equiv]

/- English proof (translation)
Establish `h` using `submatrix_mul' x y`. Rewrite `h` using `[submatrix_eq_fromBlocks, submatrix_eq_fromBlocks, submatrix_eq_fromBlocks, fromBlocks_multiply, fromBlocks_inj]`. Conclude with `h`.
-/
theorem blocks_mul (x y : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    bAA (x * y) = bAA x * bAA y + bAD x * bDA y ∧ bAD (x * y) = bAA x * bAD y + bAD x * bDD y ∧
    bDA (x * y) = bDA x * bAA y + bDD x * bDA y ∧ bDD (x * y) = bDA x * bAD y + bDD x * bDD y := by
  have h := submatrix_mul' x y
  rw [submatrix_eq_fromBlocks, submatrix_eq_fromBlocks, submatrix_eq_fromBlocks,
    fromBlocks_multiply, fromBlocks_inj] at h
  exact h

/- English proof (translation)
Rewrite using `[← Matrix.det_submatrix_equiv_self finSumFinEquiv x, submatrix_eq_fromBlocks, hx, Matrix.det_fromBlocks_zero₂₁]`.
-/
theorem det_eq_of_bDA_eq_zero (x : Matrix (Fin (r + c)) (Fin (r + c)) F) (hx : bDA x = 0) :
    x.det = (bAA x).det * (bDD x).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv x, submatrix_eq_fromBlocks, hx,
    Matrix.det_fromBlocks_zero₂₁]

/- English proof (translation)
Introduce `F _ r c p q hp hq`. Take `⟨h11, -, h21, h22⟩` from `blocks_mul (p : Matrix (Fin (r + c)) (Fin (r + c)) F) (q : Matrix _ _ F)`. Use `⟨?_, ?_, ?_, det_eq_of_bDA_eq_zero _ hp, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, h21, hp, hq]`. Simplify using the standard rewrite rules.

Rewrite using `[Units.val_mul, h11, hq]`. Simplify using the standard rewrite rules. Rewrite using `[Units.val_mul, h22, hp]`. Simplify using the standard rewrite rules. Take `⟨k11, -, k21, -⟩` from `blocks_mul ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) (p : Matrix _ _ F)`.

Establish `hone : ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) * (p : Matrix _ _ F) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Rewrite `k11`, `k21` using `[hone, hp, Matrix.mul_zero, add_zero]`. Establish `e11 : bAA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1`. Use extensionality with `i j`.

Simplify using `[bAA, Matrix.one_apply]`. Establish `e21 : bDA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0`. Use extensionality with `i j`. Simplify using `[bDA, Matrix.one_apply, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.

Rewrite `k11` using `[e11]`. Rewrite `k21` using `[e21]`. Establish `hA : bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1` using `mul_eq_one_comm.mp k11.symm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hA, Matrix.mul_one]`.

Use `_ = 0 := by rw [← Matrix.mul_assoc, ← k21, Matrix.zero_mul]`.
-/
theorem main : ∀ (F : Type) [Field F] (r c : ℕ) (p q : GL (Fin (r + c)) F), bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 ∧ bAA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ bDD ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bDD (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ (p : Matrix (Fin (r + c)) (Fin (r + c)) F).det = (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ∧ bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
  intro F _ r c p q hp hq
  obtain ⟨h11, -, h21, h22⟩ := blocks_mul (p : Matrix (Fin (r + c)) (Fin (r + c)) F) (q : Matrix _ _ F)
  refine ⟨?_, ?_, ?_, det_eq_of_bDA_eq_zero _ hp, ?_⟩
  · rw [Units.val_mul, h21, hp, hq]; simp
  · rw [Units.val_mul, h11, hq]; simp
  · rw [Units.val_mul, h22, hp]; simp
  · obtain ⟨k11, -, k21, -⟩ := blocks_mul ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)
      (p : Matrix _ _ F)
    have hone : ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) * (p : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hone, hp, Matrix.mul_zero, add_zero] at k11 k21
    have e11 : bAA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
      ext i j; simp [bAA, Matrix.one_apply]
    have e21 : bDA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
      ext i j; simp [bDA, Matrix.one_apply, Fin.ext_iff]; omega
    rw [e11] at k11
    rw [e21] at k21
    have hA : bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 :=
      mul_eq_one_comm.mp k11.symm
    calc bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)
        = bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) *
            (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)) := by
          rw [hA, Matrix.mul_one]
      _ = 0 := by rw [← Matrix.mul_assoc, ← k21, Matrix.zero_mul]

end GlobalTheory.HQStepBlocks
