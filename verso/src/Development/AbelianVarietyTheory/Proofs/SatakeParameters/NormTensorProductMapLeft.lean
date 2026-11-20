import Mathlib
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Set `e` to `Module.finBasis R L`. Set `b` to `Algebra.TensorProduct.basis B e`. Set `σ` to `Algebra.TensorProduct.map f (AlgHom.id R L)`. Establish `hrepr : ∀ z : B ⊗[R] L, ∀ i, b.repr (σ z) i = f (b.repr z i)`. Introduce `z i`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`. Simplify using `only [σ, b, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.

Establish `hb : ∀ j, σ (b j) = b j`. Introduce `j`. Simplify using `[σ, b, Algebra.TensorProduct.basis_apply]`. Establish `hmat : Algebra.leftMulMatrix b (σ w) = (Algebra.leftMulMatrix b w).map f`. Use extensionality with `i j`.

Rewrite using `[Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, ← hb j, ← map_mul, hb j, hrepr]`. Rewrite using `[Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, hmat]`. Conclude with `(AlgHom.map_det f _).symm`.
-/
theorem norm_tensorProduct_map_left {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L]
    [Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L) :
    Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by
  classical
  let e := Module.finBasis R L
  let b := Algebra.TensorProduct.basis B e
  let σ := Algebra.TensorProduct.map f (AlgHom.id R L)
  have hrepr : ∀ z : B ⊗[R] L, ∀ i, b.repr (σ z) i = f (b.repr z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [σ, b, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hb : ∀ j, σ (b j) = b j := by
    intro j
    simp [σ, b, Algebra.TensorProduct.basis_apply]
  have hmat : Algebra.leftMulMatrix b (σ w) = (Algebra.leftMulMatrix b w).map f := by
    ext i j
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      ← hb j, ← map_mul, hb j, hrepr]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, hmat]
  exact (AlgHom.map_det f _).symm

end GlobalTheory
