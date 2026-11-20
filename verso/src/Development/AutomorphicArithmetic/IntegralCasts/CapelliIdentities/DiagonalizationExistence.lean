import Mathlib

/- English proof (translation)
Introduce `κ _ n M a ha hM`. Establish `hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i)`. Introduce `i`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM, Polynomial.IsRoot.def, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`.

Use `choose v hv using fun i => (hev i).exists_hasEigenvector`. Establish `hli : LinearIndependent κ v` using `Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) a ha v hv`. Establish `hU : IsUnit (Matrix.of fun r c => v c r : Matrix (Fin n) (Fin n) κ)` using `Matrix.linearIndependent_cols_iff_isUnit.mp hli`. Take `⟨P, hP⟩` from `hU`. Use `⟨P, ?_⟩` and prove the remaining obligations.

Rewrite using `[hP]`. Use extensionality with `r c`. Establish `h` using `congrFun (hv c).apply_eq_smul r`. Rewrite `h` using `[Matrix.toLin'_apply]`. Rewrite using `[Matrix.mul_diagonal, Matrix.mul_apply]`.

Simplify `h` using `[Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem UpperTheory.Reformulated.B.DiagonalizationExistence.exists_diag :
    ∀ {κ : Type} [inst : Field κ] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) κ) (a : Fin n → κ),
    Function.Injective a →
      M.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : κ → Polynomial κ) (a i)) →
        ∃ (P : GL (Fin n) κ),
          M * (↑P : Matrix (Fin n) (Fin n) κ) = (↑P : Matrix (Fin n) (Fin n) κ) * Matrix.diagonal a := by
  intro κ _ n M a ha hM
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent κ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) a ha v hv
  have hU : IsUnit (Matrix.of fun r c => v c r : Matrix (Fin n) (Fin n) κ) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli
  obtain ⟨P, hP⟩ := hU
  refine ⟨P, ?_⟩
  rw [hP]
  ext r c
  have h := congrFun (hv c).apply_eq_smul r
  rw [Matrix.toLin'_apply] at h
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h
