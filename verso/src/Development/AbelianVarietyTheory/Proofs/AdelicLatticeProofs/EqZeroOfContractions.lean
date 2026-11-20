import Mathlib

namespace GlobalTheory.CoefficientContraction

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v w => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem coeff_eq_contraction {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] {κ : Type} [DecidableEq κ] (b : Module.Basis κ ℚ W) (i : κ)
    (t : TensorProduct ℚ V W) :
    TensorProduct.equivFinsuppOfBasisRight b t i
      = TensorProduct.rid ℚ V (LinearMap.lTensor V (b.coord i) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace ℚ W`. Apply `(TensorProduct.equivFinsuppOfBasisRight (M := V) b).injective` to reduce the goal to its premises. Use extensionality with `i`. Rewrite using `[coeff_eq_contraction, h, map_zero, Finsupp.zero_apply]`.
-/
theorem eq_zero_of_contractions {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (t : TensorProduct ℚ V W)
    (h : ∀ m : W →ₗ[ℚ] ℚ, TensorProduct.rid ℚ V (LinearMap.lTensor V m t) = 0) : t = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℚ W
  apply (TensorProduct.equivFinsuppOfBasisRight (M := V) b).injective
  ext i
  rw [coeff_eq_contraction, h, map_zero, Finsupp.zero_apply]

end GlobalTheory.CoefficientContraction
