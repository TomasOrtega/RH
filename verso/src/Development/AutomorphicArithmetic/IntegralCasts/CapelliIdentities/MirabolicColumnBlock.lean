import Mathlib

namespace UpperTheory.Reformulated.B.MirabolicColumnBlock

/- English proof (translation)
Establish `hev : ∀ a, ∃ v : Fin n → K, Module.End.HasEigenvector (Matrix.toLin' M) (d a) v`. Introduce `a`. Apply `Module.End.HasEigenvalue.exists_hasEigenvector` to reduce the goal to its premises. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM, Polynomial.IsRoot.def, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ a) (by simp)`.

Use `choose v hv using hev`. Establish `hli : LinearIndependent K v` using `Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) d hd v hv`. Establish `hu : IsUnit (Matrix.of v).transpose`. Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`. Conclude with `hli`.

Establish `hmul : M * (Matrix.of v).transpose = (Matrix.of v).transpose * Matrix.diagonal d`. Use extensionality with `i a`. Establish `h` using `congrFun (hv a).apply_eq_smul i`. Rewrite `h` using `[Matrix.toLin'_apply]`. Rewrite using `[Matrix.mul_diagonal, mul_comm]`.

Simplify `h` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Take `⟨u, hu⟩` from `hu`. Use `⟨u, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hu, hmul, ← hu, ← Matrix.mul_assoc]`. Simplify using the standard rewrite rules.
-/
theorem conj_diagonal {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.charpoly = ∏ a, (Polynomial.X - Polynomial.C (d a))) :
    ∃ h : GL (Fin n) K, ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * h = Matrix.diagonal d := by
  have hev : ∀ a, ∃ v : Fin n → K, Module.End.HasEigenvector (Matrix.toLin' M) (d a) v := by
    intro a
    apply Module.End.HasEigenvalue.exists_hasEigenvector
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  choose v hv using hev
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) d hd v hv
  have hu : IsUnit (Matrix.of v).transpose := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  have hmul : M * (Matrix.of v).transpose = (Matrix.of v).transpose * Matrix.diagonal d := by
    ext i a
    have h := congrFun (hv a).apply_eq_smul i
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_⟩
  rw [Matrix.mul_assoc, hu, hmul, ← hu, ← Matrix.mul_assoc]
  simp

end UpperTheory.Reformulated.B.MirabolicColumnBlock
