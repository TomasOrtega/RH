import Formalism.SatakeDualWeyl.Statement

namespace Formalism.UG.P

open Matrix MvPolynomial

/- English proof (translation)
Introduce `O _ n _ _ g h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.UG.stdAct`. Rewrite using `[Units.val_mul, Matrix.mulVecLin_mul]`. Unfold `Formalism.UG.stdAct`.

Rewrite using `[Units.val_one, Matrix.mulVecLin_one]`.
-/
theorem standard_action_mul_holds : Formalism.UG.StdActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.stdAct
    rw [Units.val_mul, Matrix.mulVecLin_mul]
  · unfold Formalism.UG.stdAct
    rw [Units.val_one, Matrix.mulVecLin_one]

/- English proof (translation)
Introduce `O _ n _ _ k g h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.UG.tensAct`. Rewrite using `[← PiTensorProduct.map_comp]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `(standard_action_mul_holds O n g h).1`. Unfold `Formalism.UG.tensAct`. Establish `: (fun _ : Fin k => Formalism.UG.stdAct O n 1) = fun _ => LinearMap.id`. Use function extensionality and compare the values at `fun _ => (standard_action_mul_holds O n 1 1).2`.

Rewrite using `[this, PiTensorProduct.map_id]`.
-/
theorem tensor_action_mul_holds : Formalism.UG.TensActMul := by
  intro O _ n _ _ k g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.tensAct
    rw [← PiTensorProduct.map_comp]
    congr 1
    funext i
    exact (standard_action_mul_holds O n g h).1
  · unfold Formalism.UG.tensAct
    have : (fun _ : Fin k => Formalism.UG.stdAct O n 1) = fun _ => LinearMap.id :=
      funext fun _ => (standard_action_mul_holds O n 1 1).2
    rw [this, PiTensorProduct.map_id]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `only [Formalism.UG.linSubst, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply]`. Simplify using `only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [Finset.sum_mul]`.
-/
theorem linSubst_comp (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (M N : Matrix n n O) :
    (Formalism.UG.linSubst O n M).comp (Formalism.UG.linSubst O n N) = Formalism.UG.linSubst O n (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [Formalism.UG.linSubst, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[Formalism.UG.linSubst, Matrix.one_apply]`.
-/
theorem linSubst_one (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Formalism.UG.linSubst O n 1 = AlgHom.id O _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [Formalism.UG.linSubst, Matrix.one_apply]

/- English proof (translation)
Introduce `O _ n _ _ g h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.UG.polyAct`. Rewrite using `[linSubst_comp, _root_.mul_inv_rev, Units.val_mul]`. Unfold `Formalism.UG.polyAct`.

Rewrite using `[inv_one, Units.val_one, linSubst_one]`.
-/
theorem polynomial_action_mul_holds : Formalism.UG.PolyActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.polyAct
    rw [linSubst_comp, _root_.mul_inv_rev, Units.val_mul]
  · unfold Formalism.UG.polyAct
    rw [inv_one, Units.val_one, linSubst_one]

end Formalism.UG.P
