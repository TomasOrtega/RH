import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open Finset
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramJacobi

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem det_eq_of_cols_unit {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : n → Prop) [DecidablePred p]
    (h : ∀ i j, ¬ p j → M i j = (1 : Matrix n n R) i j) :
    M.det = (M.toSquareBlockProp p).det := by
  rw [← Matrix.det_transpose, Matrix.twoBlockTriangular_det (Matrix.transpose M) p]
  · have h1 : ((Matrix.transpose M).toSquareBlockProp fun i => ¬ p i) = 1 := by
      ext i j
      simp only [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.transpose_apply,
        Matrix.submatrix_apply]
      rw [h _ _ i.2, Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun e => hij (Subtype.ext e.symm))]
    rw [h1, Matrix.det_one, mul_one, ← Matrix.det_transpose]
    rfl
  · intro i hi j hj
    rw [Matrix.transpose_apply, h _ _ hi, Matrix.one_apply_ne]
    rintro rfl
    exact hi hj

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem jacobi_minor {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (G H : Matrix n n R) (hHG : H * G = 1) (p : n → Prop) [DecidablePred p] :
    (H.toSquareBlockProp fun i => ¬ p i).det * G.det = (G.toSquareBlockProp p).det := by
  have hGH : G * H = 1 := mul_eq_one_comm.mp hHG
  let N : Matrix n n R := Matrix.of fun i j => if p j then (1 : Matrix n n R) i j else H i j
  have hN : N.det = (H.toSquareBlockProp fun i => ¬ p i).det := by
    rw [Matrix.twoBlockTriangular_det N p]
    · have h1 : N.toSquareBlockProp p = 1 := by
        ext i j
        simp only [N, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.of_apply, if_pos j.2]
        rw [Matrix.one_apply, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (fun e => hij (Subtype.ext e))]
      have h2 : (N.toSquareBlockProp fun i => ¬ p i) = H.toSquareBlockProp fun i => ¬ p i := by
        ext i j
        simp only [N, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.of_apply, if_neg j.2]
      rw [h1, h2, Matrix.det_one, one_mul]
    · intro i hi j hj
      simp only [N, Matrix.of_apply, if_pos hj]
      rw [Matrix.one_apply_ne]
      rintro rfl
      exact hi hj
  have hGN : (G * N).det = (G.toSquareBlockProp p).det := by
    rw [det_eq_of_cols_unit (G * N) p]
    · have : (G * N).toSquareBlockProp p = G.toSquareBlockProp p := by
        ext i j
        simp only [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.mul_apply, N, Matrix.of_apply, if_pos j.2, Matrix.one_apply, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [this]
    · intro i j hj
      rw [← hGH]
      simp only [Matrix.mul_apply, N, Matrix.of_apply, if_neg hj]
  rw [← hN, mul_comm, ← Matrix.det_mul, hGN]

end GlobalTheory.GramJacobi

namespace GlobalTheory.GramJacobi

end GlobalTheory.GramJacobi

namespace GlobalTheory

end GlobalTheory
