import Mathlib

namespace GlobalTheory.DeterminantExpansion

/- English proof (translation)
Establish `h : (M * C : Matrix (Fin m) (Fin m) V) = fun i => ∑ k : Fin g, M i k • C k`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Finset.sum_apply]`. Set `f : MultilinearMap V (fun _ : Fin m => Fin m → V) V` to `(Matrix.detRowAlternating : (Fin m → V) [⋀^Fin m]→ₗ[V] V).toMultilinearMap`. Establish `hf : ∀ A : Matrix (Fin m) (Fin m) V, Matrix.det A = f A` using `fun A => rfl`.

Rewrite using `[hf, h, f.map_sum (fun i k => M i k • C k)]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Rewrite using `[f.map_smul_univ (fun i => M i (J i)) (fun i => C (J i)), hf, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem det_mul_expand {V : Type} [inst : CommRing V] {m g : ℕ}
    (M : Matrix (Fin m) (Fin g) V) (C : Matrix (Fin g) (Fin m) V) :
    Matrix.det (M * C) =
      ∑ J : Fin m → Fin g, (∏ i : Fin m, M i (J i)) * Matrix.det (Matrix.submatrix C J id) := by
  classical
  have h : (M * C : Matrix (Fin m) (Fin m) V) = fun i => ∑ k : Fin g, M i k • C k := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  let f : MultilinearMap V (fun _ : Fin m => Fin m → V) V :=
    (Matrix.detRowAlternating : (Fin m → V) [⋀^Fin m]→ₗ[V] V).toMultilinearMap
  have hf : ∀ A : Matrix (Fin m) (Fin m) V, Matrix.det A = f A := fun A => rfl
  rw [hf, h, f.map_sum (fun i k => M i k • C k)]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [f.map_smul_univ (fun i => M i (J i)) (fun i => C (J i)), hf, smul_eq_mul]
  rfl

end GlobalTheory.DeterminantExpansion
