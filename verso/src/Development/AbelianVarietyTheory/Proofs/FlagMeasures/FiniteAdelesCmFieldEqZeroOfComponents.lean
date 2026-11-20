import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

namespace GlobalTheory

open Classical in

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m n`. Simplify using `[TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem equivFinsuppOfBasisLeft_lTensor {K M N N' ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] [DecidableEq ι]
    (b : Module.Basis ι K M) (f : N →ₗ[K] N') (x : M ⊗[K] N) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (LinearMap.lTensor M f x) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/- English proof (translation)
Use `set K := maximalRealSubfield L`. Set `b` to `Module.finBasis K L`. Set `e` to `TensorProduct.equivFinsuppOfBasisLeft (N := AFplus L) b`. Establish `hc : ∀ i, e a i = 0`. Introduce `i`.

Use `RestrictedProduct.ext _ _ (fun v => ?_)` and prove the remaining obligations. Establish `h1 : ∀ x, ReciprocityTheory.Aut.compAt L v x = LinearMap.lTensor L (ReciprocityTheory.Aut.evalAt L v).toLinearMap x`. Introduce `x`. Simplify using `only [ReciprocityTheory.Aut.compAt]`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul m n => simp [Algebra.TensorProduct.map_tmul]`. Consider the case `add x y hx hy => simp only [map_add] at *`. Rewrite using `[hx, hy]`. Establish `h2` using `equivFinsuppOfBasisLeft_lTensor b (ReciprocityTheory.Aut.evalAt L v).toLinearMap a i`.

Rewrite `h2` using `[← h1 a, h v, map_zero, Finsupp.zero_apply]`. Conclude with `h2.symm`. Establish `: e a = 0` using `Finsupp.ext hc`. Simplify using `using congrArg e.symm this`.
-/
theorem AL_eq_zero_of_compAt (L : Type) [Field L] [NumberField L] (a : ReciprocityTheory.Aut.AL L)
    (h : ∀ v, ReciprocityTheory.Aut.compAt L v a = 0) : a = 0 := by
  classical
  set K := maximalRealSubfield L
  let b := Module.finBasis K L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := AFplus L) b
  have hc : ∀ i, e a i = 0 := by
    intro i
    refine RestrictedProduct.ext _ _ (fun v => ?_)
    have h1 : ∀ x, ReciprocityTheory.Aut.compAt L v x =
        LinearMap.lTensor L (ReciprocityTheory.Aut.evalAt L v).toLinearMap x := by
      intro x
      simp only [ReciprocityTheory.Aut.compAt]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m n => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
    have h2 := equivFinsuppOfBasisLeft_lTensor b (ReciprocityTheory.Aut.evalAt L v).toLinearMap a i
    rw [← h1 a, h v, map_zero, Finsupp.zero_apply] at h2
    exact h2.symm
  have : e a = 0 := Finsupp.ext hc
  simpa using congrArg e.symm this

end GlobalTheory
