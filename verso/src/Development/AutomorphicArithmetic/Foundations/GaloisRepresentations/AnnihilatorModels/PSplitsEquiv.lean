import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `R S B _ _ _ _ _ I e`. Set `z : I → (S →ₐ[R] B)` to `fun i => (((Pi.evalAlgHom B (fun _ => B) i).comp e.toAlgHom).restrictScalars R).comp Algebra.TensorProduct.includeRight`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `h : ∀ x, splitMap z x = e x`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp [hx, hy]`. Consider the case `tmul b s`. Use function extensionality and compare the values at `i`.

Establish `hb : b ⊗ₜ[R] s = b • ((1 : B) ⊗ₜ[R] s)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[splitMap_tmul, hb, map_smul, Pi.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression. Establish `hf : (splitMap z : B ⊗[R] S → (I → B)) = e` using `funext h`.

Unfold `Splits`. Rewrite using `[hf]`. Conclude with `e.bijective`.
-/
theorem UpperTheory.Gal.crystallineComparison.splitsEquiv_of :
    SplitsOfEquiv := by
  intro R S B _ _ _ _ _ I e
  let z : I → (S →ₐ[R] B) := fun i =>
    (((Pi.evalAlgHom B (fun _ => B) i).comp e.toAlgHom).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  refine ⟨z, ?_⟩
  have h : ∀ x, splitMap z x = e x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul b s =>
      funext i
      have hb : b ⊗ₜ[R] s = b • ((1 : B) ⊗ₜ[R] s) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [splitMap_tmul, hb, map_smul, Pi.smul_apply, smul_eq_mul]
      rfl
  have hf : (splitMap z : B ⊗[R] S → (I → B)) = e := funext h
  unfold Splits
  rw [hf]
  exact e.bijective
