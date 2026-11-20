import Mathlib

namespace GlobalTheory.DeterminantProductExpansion

/- English proof (translation)
Set `g : Fin i → Fin N → (Fin i → R)` to `fun a k => A a k • (fun j => B k j)`. Establish `hrow : (A * B : Matrix (Fin i) (Fin i) R) = Matrix.of (fun a => ∑ k : Fin N, g a k)`. Use extensionality with `a j`. Simplify using `[g, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Establish `h1 : Matrix.det (A * B) = (Matrix.detRowAlternating : (Fin i → R) [⋀^Fin i]→ₗ[R] R).toMultilinearMap (fun a => ∑ k : Fin N, g a k)`.

Rewrite using `[hrow]`. Both sides reduce to the same expression. Rewrite using `[h1, MultilinearMap.map_sum]`. Use `Finset.sum_congr rfl (fun f _ => ?_)` and prove the remaining obligations. Simplify using `only [g]`.

Rewrite using `[MultilinearMap.map_smul_univ, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem det_mul_expand {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R) :
    Matrix.det (A * B) = ∑ f : Fin i → Fin N, (∏ a : Fin i, A a (f a)) * Matrix.det (Matrix.submatrix B f id) := by
  let g : Fin i → Fin N → (Fin i → R) := fun a k => A a k • (fun j => B k j)
  have hrow : (A * B : Matrix (Fin i) (Fin i) R) = Matrix.of (fun a => ∑ k : Fin N, g a k) := by
    ext a j
    simp [g, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : Matrix.det (A * B) =
      (Matrix.detRowAlternating : (Fin i → R) [⋀^Fin i]→ₗ[R] R).toMultilinearMap (fun a => ∑ k : Fin N, g a k) := by
    rw [hrow]; rfl
  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  simp only [g]
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

/- English proof (translation)
Introduce `A B` and use `det_mul_expand A B`.
-/
theorem main : ∀ {R : Type} [inst : CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R), Matrix.det (A * B) = ∑ f : Fin i → Fin N, (∏ a : Fin i, A a (f a)) * Matrix.det (Matrix.submatrix B f id) :=
  fun A B => det_mul_expand A B

end GlobalTheory.DeterminantProductExpansion
