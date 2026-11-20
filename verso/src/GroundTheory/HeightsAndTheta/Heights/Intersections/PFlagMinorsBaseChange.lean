import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagMinorsBaseChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCauchyBinet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

namespace FlagMinorsBaseChange

/- English proof (translation)
Establish `hle : (j : ℕ) + 1 ≤ n` using `by have := j.2; omega`. Establish `hsplit : N.submatrix (Fin.castLE hle) (S.1.orderEmbOfFin S.2) = (M.submatrix (Fin.castLE hle) id : Matrix (Fin ((j : ℕ) + 1)) (Fin m) (MvPolynomial σ F)) * ((D.map (C : F → MvPolynomial σ F)).submatrix id (S.1.orderEmbOfFin S.2) : Matrix (Fin m) (Fin ((j : ℕ) + 1)) (MvPolynomial …`. Use extensionality with `a b`. Rewrite using `[Matrix.submatrix_apply, hN, Matrix.mul_apply]`. Both sides reduce to the same expression.

Unfold `flagMinor`. Rewrite using `[hsplit, GroundTheory.Heights₂.Heights.CauchyBinet.proof]`. Use `Subalgebra.sum_mem _ fun I _ => Subalgebra.mul_mem _ ?_ ?_` and prove the remaining obligations. Apply `Algebra.subset_adjoin` to reduce the goal to its premises. Conclude with `⟨⟨j, I⟩, rfl⟩`.

Establish `h : rowsOf ((D.map (C : F → MvPolynomial σ F)).submatrix id (S.1.orderEmbOfFin S.2)) I = (RingHom.mapMatrix (C : F →+* MvPolynomial σ F)) (D.submatrix (I.1.orderEmbOfFin I.2) (S.1.orderEmbOfFin S.2))`. Use extensionality with `a b`. Both sides reduce to the same expression. Rewrite using `[h, ← RingHom.map_det]`. Conclude with `Subalgebra.algebraMap_mem _ _`.
-/
theorem flagMinor_mul_const_mem {F : Type} [Field F] {σ : Type} {n m p : ℕ}
    (M : Matrix (Fin n) (Fin m) (MvPolynomial σ F)) (D : Matrix (Fin m) (Fin p) F)
    (N : Matrix (Fin n) (Fin p) (MvPolynomial σ F)) (hN : ∀ a b, N a b = ∑ k, M a k * C (D k b))
    (j : Fin (n - 1)) (S : PluckerBlocks p n j) :
    flagMinor N j S ∈
      Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks m n j => flagMinor M q.1 q.2) := by
  have hle : (j : ℕ) + 1 ≤ n := by have := j.2; omega
  have hsplit : N.submatrix (Fin.castLE hle) (S.1.orderEmbOfFin S.2) =
      (M.submatrix (Fin.castLE hle) id : Matrix (Fin ((j : ℕ) + 1)) (Fin m) (MvPolynomial σ F)) *
        ((D.map (C : F → MvPolynomial σ F)).submatrix id (S.1.orderEmbOfFin S.2) :
          Matrix (Fin m) (Fin ((j : ℕ) + 1)) (MvPolynomial σ F)) := by
    ext a b
    rw [Matrix.submatrix_apply, hN, Matrix.mul_apply]
    rfl
  unfold flagMinor
  rw [hsplit, GroundTheory.Heights₂.Heights.CauchyBinet.proof]
  refine Subalgebra.sum_mem _ fun I _ => Subalgebra.mul_mem _ ?_ ?_
  · apply Algebra.subset_adjoin
    exact ⟨⟨j, I⟩, rfl⟩
  · have h : rowsOf ((D.map (C : F → MvPolynomial σ F)).submatrix id (S.1.orderEmbOfFin S.2)) I =
        (RingHom.mapMatrix (C : F →+* MvPolynomial σ F))
          (D.submatrix (I.1.orderEmbOfFin I.2) (S.1.orderEmbOfFin S.2)) := by
      ext a b
      rfl
    rw [h, ← RingHom.map_det]
    exact Subalgebra.algebraMap_mem _ _

/- English proof (translation)
Establish `hinj : Function.Injective B.vecMul` using `Matrix.vecMul_injective_iff.mpr hB`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective B.vecMulLinear (LinearMap.ker_eq_bot.mpr hinj)`. Use `⟨(LinearMap.toMatrix' g).transpose, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.ext_iff_vecMul]`. Introduce `v`.

Rewrite using `[← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, Matrix.vecMul_one]`. Conclude with `congrFun (congrArg DFunLike.coe hg) v`.
-/
theorem exists_mul_eq_one {F : Type} [Field F] {n N1 : ℕ} (B : Matrix (Fin n) (Fin N1) F)
    (hB : LinearIndependent F B) : ∃ D : Matrix (Fin N1) (Fin n) F, B * D = 1 := by
  have hinj : Function.Injective B.vecMul := Matrix.vecMul_injective_iff.mpr hB
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective B.vecMulLinear
    (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨(LinearMap.toMatrix' g).transpose, ?_⟩
  rw [Matrix.ext_iff_vecMul]
  intro v
  rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, Matrix.vecMul_one]
  exact congrFun (congrArg DFunLike.coe hg) v

end FlagMinorsBaseChange

/- English proof (translation)
Introduce `F _ n N1 B hB`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `FlagMinorsBaseChange.flagMinor_mul_const_mem (genMat F n) B _ (fun a b => rfl) q.1 q.2`.

Take `⟨D, hD⟩` from `FlagMinorsBaseChange.exists_mul_eq_one B hB`. Establish `e : ∀ l b, ∑ k, B l k * D k b = (1 : Matrix (Fin n) (Fin n) F) l b` using `fun l b => by`. Rewrite using `[← Matrix.mul_apply, hD]`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨q, rfl⟩`.

Use `FlagMinorsBaseChange.flagMinor_mul_const_mem _ D (genMat F n) ?_ q.1 q.2` and prove the remaining obligations. Introduce `a b`. Use `show X (a, b) = ∑ k, (∑ l, X (a, l) * C (B l k)) * C (D k b)`. Use `symm`. Repeatedly rewrite using `[Finset.sum_mul, mul_assoc, ← map_mul]`.

Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.mul_sum, ← map_sum, e, Matrix.one_apply]`. Simplify using the standard rewrite rules.
-/
theorem FlagMinorsBaseChange.proof : FlagMinorsBaseChange.Statement := by
  intro F _ n N1 B hB
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    exact FlagMinorsBaseChange.flagMinor_mul_const_mem (genMat F n) B _ (fun a b => rfl) q.1 q.2
  · obtain ⟨D, hD⟩ := FlagMinorsBaseChange.exists_mul_eq_one B hB
    have e : ∀ l b, ∑ k, B l k * D k b = (1 : Matrix (Fin n) (Fin n) F) l b := fun l b => by
      rw [← Matrix.mul_apply, hD]
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    refine FlagMinorsBaseChange.flagMinor_mul_const_mem _ D (genMat F n) ?_ q.1 q.2
    intro a b
    show X (a, b) = ∑ k, (∑ l, X (a, l) * C (B l k)) * C (D k b)
    symm
    simp_rw [Finset.sum_mul, mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← map_sum, e, Matrix.one_apply]
    simp

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
