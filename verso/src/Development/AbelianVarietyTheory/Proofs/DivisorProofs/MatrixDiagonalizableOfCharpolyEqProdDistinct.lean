import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem matrix_diagonalizable_of_charpoly_eq_prod_distinct (K : Type) [Field K] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (ν : Fin n → K) (hν : Function.Injective ν)
    (hγ : γ.charpoly = ∏ k, (X - C (ν k))) :
    ∃ y : GL (Fin n) K, γ * (y : Matrix (Fin n) (Fin n) K) = (y : Matrix (Fin n) (Fin n) K) * Matrix.diagonal ν := by
  have hev : ∀ k, Module.End.HasEigenvalue (Matrix.toLin' γ) (ν k) := by
    intro k
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hγ]
    simp only [IsRoot, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)
  choose v hv using fun k => (hev k).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ ν hν v hv
  set Y : Matrix (Fin n) (Fin n) K := Matrix.of fun i k => v k i with hY
  have hcols : Y.col = v := by
    funext k i; rfl
  have hu : IsUnit Y := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    rw [hcols]; exact hli
  refine ⟨hu.unit, ?_⟩
  simp only [IsUnit.unit_spec]
  ext i k
  rw [Matrix.mul_diagonal]
  have h1 := (hv k).apply_eq_smul
  rw [Matrix.toLin'_apply] at h1
  have h2 := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  rw [Matrix.mul_apply]
  simp only [hY, Matrix.of_apply]
  rw [mul_comm, ← h2]
  rfl

end GlobalTheory
