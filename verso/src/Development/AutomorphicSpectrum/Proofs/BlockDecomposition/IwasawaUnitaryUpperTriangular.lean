import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.QR

/- English proof (translation)
Set `e` to `EuclideanSpace.basisFun (Fin m) ℂ`. Set `f : Fin m → EuclideanSpace ℂ (Fin m)` to `fun j => WithLp.toLp 2 fun i => g i j`. Establish `h : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m)` using `by simp`. Set `o` to `InnerProductSpace.gramSchmidtOrthonormalBasis h f`. Use `⟨e.toBasis.toMatrix o, e.toMatrix_orthonormalBasis_mem_unitary o, o.toBasis.toMatrix f, ?_, InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f⟩` and prove the remaining obligations.

Establish `hmul` using `Module.Basis.toMatrix_mul_toMatrix e.toBasis o.toBasis f`. Rewrite `hmul` using `[OrthonormalBasis.coe_toBasis]`. Rewrite using `[hmul]`. Use extensionality with `i j`. Rewrite using `[Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]`.
-/
theorem exists_unitary_mul_blockTriangular {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (_hg : IsUnit g) :
    ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ,
      g = k * b ∧ b.BlockTriangular id := by
  let e := EuclideanSpace.basisFun (Fin m) ℂ
  let f : Fin m → EuclideanSpace ℂ (Fin m) := fun j => WithLp.toLp 2 fun i => g i j
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by simp
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  refine ⟨e.toBasis.toMatrix o, e.toMatrix_orthonormalBasis_mem_unitary o, o.toBasis.toMatrix f, ?_,
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f⟩
  have hmul := Module.Basis.toMatrix_mul_toMatrix e.toBasis o.toBasis f
  rw [OrthonormalBasis.coe_toBasis] at hmul
  rw [hmul]
  ext i j
  rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]

end GlobalTheory.CompanionTheory.QR
