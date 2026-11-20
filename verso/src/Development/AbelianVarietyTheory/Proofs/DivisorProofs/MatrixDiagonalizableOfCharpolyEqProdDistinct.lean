import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `hev : ∀ k, Module.End.HasEigenvalue (Matrix.toLin' γ) (ν k)`. Introduce `k`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hγ]`. Simplify using `only [IsRoot, eval_prod, eval_sub, eval_X, eval_C]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)`.

Use `choose v hv using fun k => (hev k).exists_hasEigenvector`. Establish `hli : LinearIndependent K v` using `Module.End.eigenvectors_linearIndependent' _ ν hν v hv`. Use `set Y : Matrix (Fin n) (Fin n) K := Matrix.of fun i k => v k i with hY`. Establish `hcols : Y.col = v`. Use function extensionality and compare the values at `k i`.

Both sides reduce to the same expression. Establish `hu : IsUnit Y`. Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`. Rewrite using `[hcols]`. Conclude with `hli`.

Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Simplify using `only [IsUnit.unit_spec]`. Use extensionality with `i k`. Rewrite using `[Matrix.mul_diagonal]`. Establish `h1` using `(hv k).apply_eq_smul`.

Rewrite `h1` using `[Matrix.toLin'_apply]`. Establish `h2` using `congrFun h1 i`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h2`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hY, Matrix.of_apply]`.

Rewrite using `[mul_comm, ← h2]`. Both sides reduce to the same expression.
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
