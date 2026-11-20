import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersSurjectiveOfRankOne

open UpperTheory.Gal.Int.Geo

/- English proof (translation)
Use `⟨{ toFun := fun M => M default default invFun := fun a => Matrix.of fun _ _ => a left_inv := ?_ right_inv := ?_ map_mul' := ?_ map_add' := ?_ commutes' := ?_ }⟩` and prove the remaining obligations. Introduce `M`. Use extensionality with `i j`. Simplify using `[Subsingleton.elim i default, Subsingleton.elim j default]`. Introduce `a`.

Simplify using the standard rewrite rules. Introduce `M N`. Simplify using `[Matrix.mul_apply]`. Introduce `M N`. Simplify using the standard rewrite rules.

Introduce `r`. Simplify using `[Matrix.algebraMap_matrix_apply]`.
-/
private theorem matrix_unique_algEquiv (R A m : Type) [CommSemiring R] [Semiring A] [Algebra R A]
    [fm : Fintype m] [dm : DecidableEq m] [Unique m] : Nonempty (Matrix m m A ≃ₐ[R] A) := by
  refine ⟨{ toFun := fun M => M default default
            invFun := fun a => Matrix.of fun _ _ => a
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_
            map_add' := ?_
            commutes' := ?_ }⟩
  · intro M
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  · intro a
    simp
  · intro M N
    simp [Matrix.mul_apply]
  · intro M N
    simp
  · intro r
    simp [Matrix.algebraMap_matrix_apply]

open scoped TensorProduct in
/- English proof (translation)
Introduce `p _ D hm q _`. Use `haveI : Unique (Fin D.m) := { default := ⟨0, by omega⟩ uniq := fun i => Fin.ext (by have := i.2; simp; omega) }`. Set `e0 : D.O ≃ₐ[NumberField.RingOfIntegers D.F] NumberField.RingOfIntegers D.F` to `(AlgEquiv.ofBijective (Algebra.ofId _ _) ⟨D.algebraMap_injective hm, GlobalTheory.T.integers_surjective_of_rank_one p D hm⟩).symm`. Conclude with `⟨(Algebra.TensorProduct.congr e0 AlgEquiv.refl).trans (matrix_unique_algEquiv _ _ _).some.symm⟩`.
-/
theorem UpperTheory.rational_splitting_exists :
    SplitQ := by
  intro p _ D hm q _
  haveI : Unique (Fin D.m) :=
    { default := ⟨0, by omega⟩
      uniq := fun i => Fin.ext (by have := i.2; simp; omega) }
  let e0 : D.O ≃ₐ[NumberField.RingOfIntegers D.F] NumberField.RingOfIntegers D.F :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _)
      ⟨D.algebraMap_injective hm, GlobalTheory.T.integers_surjective_of_rank_one p D hm⟩).symm
  exact ⟨(Algebra.TensorProduct.congr e0 AlgEquiv.refl).trans
    (matrix_unique_algEquiv _ _ _).some.symm⟩
