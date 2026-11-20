import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `R R' S B _ _ _ _ _ _ _ _ _ I z hz`. Set `z' : I → (R' ⊗[R] S →ₐ[R'] B)` to `fun i => Algebra.TensorProduct.lift (Algebra.ofId R' B) (z i) (fun _ _ => Commute.all _ _)`. Establish `hz' : ∀ i (r : R') (s : S), z' i (r ⊗ₜ s) = algebraMap R' B r * z i s`. Introduce `i r s`. Simplify using `[z', Algebra.ofId_apply]`.

Use `⟨z', ?_, ?_⟩` and prove the remaining obligations. Establish `key : ∀ x, splitMap z' x = splitMap z (Algebra.TensorProduct.cancelBaseChange R R' B B S x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul b y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a c ha hc => simp only [tmul_add, map_add, ha, hc]`.

Consider the case `tmul r s`. Use function extensionality and compare the values at `i`. Rewrite using `[splitMap_tmul, hz', Algebra.TensorProduct.cancelBaseChange_tmul, splitMap_tmul]`. Simplify using `[Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]`. Establish `hfun : (⇑(splitMap z') : B ⊗[R'] (R' ⊗[R] S) → (I → B)) = (splitMap z) ∘ (Algebra.TensorProduct.cancelBaseChange R R' B B S)` using `funext key`.

Unfold `Splits`. Rewrite using `[hfun]`. Conclude with `hz.comp (AlgEquiv.bijective _)`. Introduce `i s`. Rewrite using `[hz']`.

Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Gal.crystallineComparison.splitsBC_of :
    SplitsBC := by
  intro R R' S B _ _ _ _ _ _ _ _ _ I z hz
  let z' : I → (R' ⊗[R] S →ₐ[R'] B) := fun i =>
    Algebra.TensorProduct.lift (Algebra.ofId R' B) (z i) (fun _ _ => Commute.all _ _)
  have hz' : ∀ i (r : R') (s : S), z' i (r ⊗ₜ s) = algebraMap R' B r * z i s := by
    intro i r s
    simp [z', Algebra.ofId_apply]
  refine ⟨z', ?_, ?_⟩
  · have key : ∀ x, splitMap z' x =
        splitMap z (Algebra.TensorProduct.cancelBaseChange R R' B B S x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul b y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a c ha hc => simp only [tmul_add, map_add, ha, hc]
        | tmul r s =>
          funext i
          rw [splitMap_tmul, hz', Algebra.TensorProduct.cancelBaseChange_tmul, splitMap_tmul]
          simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
    have hfun : (⇑(splitMap z') : B ⊗[R'] (R' ⊗[R] S) → (I → B)) =
        (splitMap z) ∘ (Algebra.TensorProduct.cancelBaseChange R R' B B S) := funext key
    unfold Splits
    rw [hfun]
    exact hz.comp (AlgEquiv.bijective _)
  · intro i s
    rw [hz']
    simp
