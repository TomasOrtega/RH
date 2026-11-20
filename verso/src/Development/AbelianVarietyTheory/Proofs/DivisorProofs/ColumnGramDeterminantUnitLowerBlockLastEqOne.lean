import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem blkW_det_eq_one (r p0 : ℕ) (w : Low r → ℂ) : (blkW p0 w).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [blkW, lowMat]
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    simp only [blkW, lowMat]
    split_ifs with h1 h2 h3 h4 h5 h6
    all_goals first
      | rfl
      | (exfalso; simp only [Fin.lt_def, Fin.ext_iff] at *; omega)

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem colGram_blkW_last (r p0 : ℕ) (w : Low r → ℂ) :
    colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  unfold colGram lminor
  have : (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r - 1)).isLt) : Fin (r - 1) → Fin (r - 1)) = id := by
    funext i; ext; simp
  rw [this, Matrix.submatrix_id_id, Matrix.det_mul, Matrix.det_conjTranspose, blkW_det_eq_one]
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem colGramLast : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 :=
  colGram_blkW_last

end GlobalTheory.IntBall
