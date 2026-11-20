import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj

open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

def LFocks_rowMat {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ :=
  fun v w => if v.2 = w.2 then g v.1 w.1 else 0

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [rowAct, sub, aeval_X, LFocks_rowMat]`. Rewrite using `[Fintype.sum_prod_type]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `b _`. Rewrite using `[Finset.sum_eq_single v.2]`. Simplify using the standard rewrite rules. Introduce `s _ hs`. Simplify using `[Ne.symm hs]`.

Simplify using the standard rewrite rules.
-/
lemma LFocks_rowAct_eq_sub {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    rowAct ℂ (n := n) g = sub (LFocks_rowMat g) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, sub, aeval_X, LFocks_rowMat]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single v.2]
  · simp
  · intro s _ hs; simp [Ne.symm hs]
  · simp

/- English proof (translation)
Use extensionality with `v w`. Simplify using `only [Matrix.conjTranspose_apply, LFocks_rowMat]`. Distinguish the cases in `h : v.2 = w.2`. Rewrite using `[if_pos h.symm, if_pos h]`. Rewrite using `[if_neg (Ne.symm h), if_neg h, star_zero]`.
-/
lemma LFocks_rowMat_conjTranspose {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    (LFocks_rowMat (n := n) g).conjTranspose = LFocks_rowMat g.conjTranspose := by
  ext v w
  simp only [Matrix.conjTranspose_apply, LFocks_rowMat]
  by_cases h : v.2 = w.2
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

/- English proof (translation)
Introduce `r n g f h`. Rewrite using `[LFocks_rowAct_eq_sub, LFocks_rowAct_eq_sub, LFocks_subAdj, LFocks_rowMat_conjTranspose]`.
-/
theorem fischerInnerRowActionAdjoint : FockRowAdj := by
  intro r n g f h
  rw [LFocks_rowAct_eq_sub, LFocks_rowAct_eq_sub, LFocks_subAdj, LFocks_rowMat_conjTranspose]

end Formalism.GradedWeylDivisibility
