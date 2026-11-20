import Mathlib

namespace GlobalTheory.UnitaryUpperTriangular

open Module InnerProductSpace

/- English proof (translation)
Set `f : Fin n → EuclideanSpace ℂ (Fin n)` to `fun i => WithLp.toLp 2 (fun k => y k i)`. Establish `h : finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n)` using `finrank_euclideanSpace`. Set `a` to `EuclideanSpace.basisFun (Fin n) ℂ`. Set `b` to `gramSchmidtOrthonormalBasis h f`. Use `⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b, b.toBasis.toMatrix f, gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f, ?_⟩` and prove the remaining obligations.

Rewrite using `[← b.coe_toBasis, Basis.toMatrix_mul_toMatrix]`. Use extensionality with `k i`. Simplify using `[Basis.toMatrix_apply, a, f]`.
-/
theorem exists_unitary_mul_upperTriangular {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ (t : Matrix (Fin n) (Fin n) ℂ),
      Matrix.BlockTriangular t id ∧ y = u * t := by
  classical
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (fun k => y k i)
  have h : finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := finrank_euclideanSpace
  let a := EuclideanSpace.basisFun (Fin n) ℂ
  let b := gramSchmidtOrthonormalBasis h f
  refine ⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b,
    b.toBasis.toMatrix f, gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f, ?_⟩
  rw [← b.coe_toBasis, Basis.toMatrix_mul_toMatrix]
  ext k i
  simp [Basis.toMatrix_apply, a, f]

end GlobalTheory.UnitaryUpperTriangular
