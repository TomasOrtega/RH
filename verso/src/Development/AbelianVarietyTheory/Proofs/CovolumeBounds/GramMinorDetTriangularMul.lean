import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

/- English proof (translation)
Use extensionality with `i b`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply, id]`. Use `symm`. Use `Finset.sum_of_injOn (Fin.castLE hj) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a _ c _ h`.

Conclude with `Fin.castLE_injective hj h`. Introduce `a _`. Conclude with `Finset.mem_univ _`. Introduce `c _ hc`. Establish `hlt : Fin.castLE hj b < c`.

Assume the negation of the conclusion as `hle`. Apply `hc` to reduce the goal to its premises. Establish `h1 : c.val ≤ b.val`. Use `not_lt.mp hle` as an intermediate fact. Conclude with `this`.

Use `⟨⟨c.val, lt_of_le_of_lt h1 b.2⟩, by simp, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[hu (show id (Fin.castLE hj b) < id c from hlt), mul_zero]`. Introduce `a _`.

Both sides reduce to the same expression.
-/
theorem submatrix_mul_upperTriangular_castLE {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (u : Matrix (Fin m) (Fin m) ℂ) {j : ℕ} (hj : j ≤ m) (hu : u.BlockTriangular id) :
    (A * u).submatrix id (Fin.castLE hj) =
      A.submatrix id (Fin.castLE hj) * u.submatrix (Fin.castLE hj) (Fin.castLE hj) := by
  ext i b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hj) ?_ ?_ ?_ ?_
  · intro a _ c _ h
    exact Fin.castLE_injective hj h
  · intro a _
    exact Finset.mem_univ _
  · intro c _ hc
    have hlt : Fin.castLE hj b < c := by
      by_contra hle
      apply hc
      have h1 : c.val ≤ b.val := by
        have := not_lt.mp hle
        exact this
      refine ⟨⟨c.val, lt_of_le_of_lt h1 b.2⟩, by simp, ?_⟩
      ext
      simp
    rw [hu (show id (Fin.castLE hj b) < id c from hlt), mul_zero]
  · intro a _
    rfl

/- English proof (translation)
Introduce `n m A u j hj hu`. Establish `key : ∀ B : Matrix (Fin n) (Fin m) ℂ, (Bᴴ * B).submatrix (Fin.castLE hj) (Fin.castLE hj) = (B.submatrix id (Fin.castLE hj))ᴴ * B.submatrix id (Fin.castLE hj)`. Introduce `B`. Use extensionality with `a b`. Simplify using `[Matrix.mul_apply]`.

Establish `hu' : (u.submatrix (Fin.castLE hj) (Fin.castLE hj)).BlockTriangular id`. Introduce `a b hab`. Conclude with `hu (show id (Fin.castLE hj b) < id (Fin.castLE hj a) from hab)`. Rewrite using `[key, key, submatrix_mul_upperTriangular_castLE A u hj hu, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (u.submatrix (Fin.castLE hj) (Fin.castLE hj)), Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_of_upperTriangular hu']`. Simplify using `only [Matrix.submatrix_apply]`.

Rewrite using `[← map_prod Complex.normSq, Complex.normSq_eq_conj_mul_self, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_leading_gram_mul_upperTriangular :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ) (j : ℕ) (hj : j ≤ m), u.BlockTriangular id → (((A * u)ᴴ * (A * u)).submatrix (Fin.castLE hj) (Fin.castLE hj)).det = ((∏ b : Fin j, Complex.normSq (u (Fin.castLE hj b) (Fin.castLE hj b)) : ℝ) : ℂ) * ((Aᴴ * A).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  intro n m A u j hj hu
  have key : ∀ B : Matrix (Fin n) (Fin m) ℂ,
      (Bᴴ * B).submatrix (Fin.castLE hj) (Fin.castLE hj) =
        (B.submatrix id (Fin.castLE hj))ᴴ * B.submatrix id (Fin.castLE hj) := by
    intro B
    ext a b
    simp [Matrix.mul_apply]
  have hu' : (u.submatrix (Fin.castLE hj) (Fin.castLE hj)).BlockTriangular id := by
    intro a b hab
    exact hu (show id (Fin.castLE hj b) < id (Fin.castLE hj a) from hab)
  rw [key, key, submatrix_mul_upperTriangular_castLE A u hj hu, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (u.submatrix (Fin.castLE hj) (Fin.castLE hj)),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_of_upperTriangular hu']
  simp only [Matrix.submatrix_apply]
  rw [← map_prod Complex.normSq, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end GlobalTheory.HCXi
