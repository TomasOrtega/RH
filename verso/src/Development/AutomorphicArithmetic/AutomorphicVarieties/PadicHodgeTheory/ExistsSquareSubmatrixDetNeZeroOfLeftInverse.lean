import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

/- English proof (translation)
Introduce `B _ _ d r X Z hZX`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hM : (Z * X) = fun a => ∑ k, Z a k • X k`. Use function extensionality and compare the values at `a b`.

Simplify using `[Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]`. Establish `key : (Z * X).det = ∑ s : Fin r → Fin d, (∏ a, Z a (s a)) * (X.submatrix s id).det`. Establish `e1 : (Z * X).det = Matrix.detRowAlternating (fun a => ∑ k, Z a k • X k)`. Rewrite using `[← hM]`. Both sides reduce to the same expression.

Rewrite using `[e1]`. Establish `e2` using `(Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_sum (fun a k => Z a k • X k)`. Simplify using `only [AlternatingMap.coe_multilinearMap] at e2`. Rewrite using `[e2]`. Use `Finset.sum_congr rfl (fun s _ => ?_)` and prove the remaining obligations.

Establish `e3` using `(Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_smul_univ (fun a => Z a (s a)) (fun a => X (s a))`. Simplify using `only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at e3`. Rewrite using `[e3]`. Both sides reduce to the same expression. Establish `h0 : (Z * X).det = 0`.

Rewrite using `[key]`. Conclude with `Finset.sum_eq_zero (fun s _ => by rw [h s, mul_zero])`. Rewrite `h0` using `[hZX, Matrix.det_one]`. Conclude with `one_ne_zero h0`.
-/
theorem UpperTheory.exists_square_submatrix_det_ne_zero_of_left_inverse :
    ∀ {B : Type} [CommRing B] [IsDomain B] {d r : ℕ} (X : Matrix (Fin d) (Fin r) B) (Z : Matrix (Fin r) (Fin d) B), Z * X = 1 → ∃ s : Fin r → Fin d, (X.submatrix s id).det ≠ 0 := by
  intro B _ _ d r X Z hZX
  classical
  by_contra h
  push_neg at h
  have hM : (Z * X) = fun a => ∑ k, Z a k • X k := by
    funext a b
    simp [Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]
  have key : (Z * X).det = ∑ s : Fin r → Fin d, (∏ a, Z a (s a)) * (X.submatrix s id).det := by
    have e1 : (Z * X).det = Matrix.detRowAlternating (fun a => ∑ k, Z a k • X k) := by
      rw [← hM]
      rfl
    rw [e1]
    have e2 := (Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_sum
      (fun a k => Z a k • X k)
    simp only [AlternatingMap.coe_multilinearMap] at e2
    rw [e2]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have e3 := (Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_smul_univ
      (fun a => Z a (s a)) (fun a => X (s a))
    simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at e3
    rw [e3]
    rfl
  have h0 : (Z * X).det = 0 := by
    rw [key]
    exact Finset.sum_eq_zero (fun s _ => by rw [h s, mul_zero])
  rw [hZX, Matrix.det_one] at h0
  exact one_ne_zero h0
