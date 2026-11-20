import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SortedSpec

open Matrix Finset

noncomputable section

namespace PI.ET

/- English proof (translation)
Introduce `n A hA`. Establish `hH : A.IsHermitian` using `hA`. Use `set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU`. Establish `hUU : U * star U = 1` using `(Matrix.mem_unitaryGroup_iff).1 hH.eigenvectorUnitary.2`. Establish `hspec` using `hH.spectral_theorem`.

Use `set l : Fin n → ℝ := hH.eigenvalues with hl`. Set `σ : Equiv.Perm (Fin n)` to `Tuple.sort (fun i => OrderDual.toDual (l i))`. Establish `hmono : Monotone ((fun i => OrderDual.toDual (l i)) ∘ σ)` using `Tuple.monotone_sort _`. Use `⟨l ∘ σ, fun i j hij => hmono hij, U.submatrix id σ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, hUU, Matrix.submatrix_id_id]`.

Establish `hD : Matrix.diagonal (fun i => ((l ∘ σ) i : ℂ)) = (Matrix.diagonal (fun i => (l i : ℂ))).submatrix σ σ`. Rewrite using `[Matrix.submatrix_diagonal_equiv]`. Both sides reduce to the same expression. Rewrite using `[hD, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]`. Use `conv_lhs => rw [hspec]`.

Both sides reduce to the same expression.
-/
theorem specExists : SpecExists := by
  intro n A hA
  have hH : A.IsHermitian := hA
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hH.eigenvectorUnitary.2
  have hspec := hH.spectral_theorem
  set l : Fin n → ℝ := hH.eigenvalues with hl

  let σ : Equiv.Perm (Fin n) := Tuple.sort (fun i => OrderDual.toDual (l i))
  have hmono : Monotone ((fun i => OrderDual.toDual (l i)) ∘ σ) := Tuple.monotone_sort _
  refine ⟨l ∘ σ, fun i j hij => hmono hij, U.submatrix id σ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, hUU, Matrix.submatrix_id_id]
  · have hD : Matrix.diagonal (fun i => ((l ∘ σ) i : ℂ)) =
        (Matrix.diagonal (fun i => (l i : ℂ))).submatrix σ σ := by
      rw [Matrix.submatrix_diagonal_equiv]
      rfl
    rw [hD, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
    conv_lhs => rw [hspec]
    rfl

/- English proof (translation)
Introduce `n A d ⟨_, W, hW, hA⟩`. Establish `hWW : star W * W = 1` using `(Matrix.mem_unitaryGroup_iff').1 hW`. Rewrite `hWW` using `[Matrix.star_eq_conjTranspose]`. Use `set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (d i : ℂ) with hD`. Establish `hDh : Dᴴ = D`.

Rewrite using `[hD, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hAh : Aᴴ = W * D * Wᴴ`.

Rewrite using `[hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDh, Matrix.mul_assoc]`. Establish `key : (A * Aᴴ).trace = ∑ i, ((d i : ℂ)) ^ 2`. Rewrite using `[hAh, hA]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Wᴴ W, hWW, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hWW, Matrix.mul_one, hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]`.

Simplify using `[sq]`. Establish `lhs : (A * Aᴴ).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ)`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.star_def, Complex.mul_conj']`. Use `lhs.symm.trans key` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem hsEq : HSEq := by
  intro n A d ⟨_, W, hW, hA⟩
  have hWW : star W * W = 1 := (Matrix.mem_unitaryGroup_iff').1 hW
  rw [Matrix.star_eq_conjTranspose] at hWW
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (d i : ℂ) with hD
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hAh : Aᴴ = W * D * Wᴴ := by
    rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDh,
      Matrix.mul_assoc]
  have key : (A * Aᴴ).trace = ∑ i, ((d i : ℂ)) ^ 2 := by
    rw [hAh, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, hWW, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc, hWW, Matrix.mul_one, hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp [sq]
  have lhs : (A * Aᴴ).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  have := lhs.symm.trans key
  exact_mod_cast this

end PI.ET
