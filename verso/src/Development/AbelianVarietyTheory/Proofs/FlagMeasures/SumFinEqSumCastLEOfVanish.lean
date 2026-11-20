import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.LeadMinorTri

/- English proof (translation)
Use `symm`. Use `Finset.sum_of_injOn (Fin.castLE hl) ((Fin.castLE_injective hl).injOn) (by simp) ?_ (by simp)` and prove the remaining obligations. Introduce `k _ hk`. Apply `hf` to reduce the goal to its premises. Assume the negation of the conclusion as `h`.

Conclude with `hk ⟨⟨k.val, by omega⟩, by simp, rfl⟩`.
-/
theorem sum_fin_eq_sum_castLE_of_vanish {n l : ℕ} (hl : l ≤ n) (f : Fin n → ℂ)
    (hf : ∀ k : Fin n, l ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k : Fin l, f (Fin.castLE hl k) := by
  symm
  refine Finset.sum_of_injOn (Fin.castLE hl) ((Fin.castLE_injective hl).injOn) (by simp) ?_ (by simp)
  intro k _ hk
  apply hf
  by_contra h
  exact hk ⟨⟨k.val, by omega⟩, by simp, rfl⟩

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `sum_fin_eq_sum_castLE_of_vanish hl (fun k => c (Fin.castLE hl i) k * z k (Fin.castLE hl j)) ?_` and prove the remaining obligations. Introduce `k hk`. Rewrite using `[hc _ k (by rw [Fin.lt_def]; have := i.isLt; simp only [Fin.val_castLE]; omega), zero_mul]`.
-/
theorem leadBlock_lower_mul {n l : ℕ} (hl : l ≤ n) (c z : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, i < j → c i j = 0) :
    (c * z).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      c.submatrix (Fin.castLE hl) (Fin.castLE hl) * z.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fin_eq_sum_castLE_of_vanish hl (fun k => c (Fin.castLE hl i) k * z k (Fin.castLE hl j)) ?_
  intro k hk
  rw [hc _ k (by rw [Fin.lt_def]; have := i.isLt; simp only [Fin.val_castLE]; omega), zero_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `sum_fin_eq_sum_castLE_of_vanish hl (fun k => z (Fin.castLE hl i) k * c k (Fin.castLE hl j)) ?_` and prove the remaining obligations. Introduce `k hk`. Rewrite using `[hc k _ (by rw [Fin.lt_def]; have := j.isLt; simp only [Fin.val_castLE]; omega), mul_zero]`.
-/
theorem leadBlock_mul_upper {n l : ℕ} (hl : l ≤ n) (z c : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, j < i → c i j = 0) :
    (z * c).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      z.submatrix (Fin.castLE hl) (Fin.castLE hl) * c.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fin_eq_sum_castLE_of_vanish hl (fun k => z (Fin.castLE hl i) k * c k (Fin.castLE hl j)) ?_
  intro k hk
  rw [hc k _ (by rw [Fin.lt_def]; have := j.isLt; simp only [Fin.val_castLE]; omega), mul_zero]

/- English proof (translation)
Introduce `n c z c' hc hc' l hl`. Establish `h1 : (c.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = ∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i)`. Apply `Matrix.det_of_lowerTriangular` to reduce the goal to its premises. Introduce `i j hij`. Conclude with `hc _ _ (show i < j from hij)`.

Establish `h2 : (c'.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = ∏ i : Fin l, c' (Fin.castLE hl i) (Fin.castLE hl i)`. Apply `Matrix.det_of_upperTriangular` to reduce the goal to its premises. Introduce `i j hij`. Conclude with `hc' _ _ (show j < i from hij)`. Express the relevant statement in the definitionally equal form `((c * z * c').submatrix (Fin.castLE hl) (Fin.castLE hl)).det = _ * (z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det`.

Rewrite using `[leadBlock_mul_upper hl _ _ hc', leadBlock_lower_mul hl _ _ hc, Matrix.det_mul, Matrix.det_mul, h1, h2, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leadMinor_lower_mul_mul_upper :
    ∀ (n : ℕ) (c z c' : Matrix (Fin n) (Fin n) ℂ), (∀ i j, i < j → c i j = 0) → (∀ i j, j < i → c' i j = 0) → ∀ (l : ℕ) (hl : l ≤ n), leadMinor (c * z * c') l hl = (∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i) * c' (Fin.castLE hl i) (Fin.castLE hl i)) * leadMinor z l hl := by
  intro n c z c' hc hc' l hl
  have h1 : (c.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      ∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i) := by
    apply Matrix.det_of_lowerTriangular
    intro i j hij
    exact hc _ _ (show i < j from hij)
  have h2 : (c'.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      ∏ i : Fin l, c' (Fin.castLE hl i) (Fin.castLE hl i) := by
    apply Matrix.det_of_upperTriangular
    intro i j hij
    exact hc' _ _ (show j < i from hij)
  change ((c * z * c').submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
    _ * (z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
  rw [leadBlock_mul_upper hl _ _ hc', leadBlock_lower_mul hl _ _ hc, Matrix.det_mul, Matrix.det_mul,
    h1, h2, Finset.prod_mul_distrib]
  ring

end GlobalTheory.LeadMinorTri
