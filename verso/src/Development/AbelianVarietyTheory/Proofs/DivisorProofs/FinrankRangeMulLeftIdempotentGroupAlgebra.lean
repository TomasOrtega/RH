import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

/- English proof (translation)
Introduce `K H _ _ _ _ a ha`. Use `haveI : Fintype H := Fintype.ofFinite H`. Establish `hi : IsIdempotentElem (LinearMap.mulLeft K a)`. Express the relevant statement in the definitionally equal form `LinearMap.mulLeft K a * LinearMap.mulLeft K a = LinearMap.mulLeft K a`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `a * (a * x) = a * x`. Rewrite using `[← mul_assoc, ha]`. Rewrite using `[← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace]`. Rewrite using `[LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis H K), Matrix.trace]`. Establish `h : ∀ g : H, Matrix.diag (LinearMap.toMatrix (MonoidAlgebra.basis H K) (MonoidAlgebra.basis H K) (LinearMap.mulLeft K a)) g = a.coeff 1`.

Introduce `g`. Rewrite using `[Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply, LinearMap.mulLeft_apply]`. Express the relevant statement in the definitionally equal form `(a * MonoidAlgebra.single g 1).coeff g = a.coeff 1`. Rewrite using `[MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]`. Rewrite using `[Finset.sum_congr rfl (fun g _ => h g), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]`.
-/
theorem finrank_range_mulLeft_idem : ∀ (K H : Type) [Field K] [CharZero K] [Group H] [Finite H] (a : MonoidAlgebra K H), a * a = a → ((finrank K (LinearMap.range (LinearMap.mulLeft K a)) : ℕ) : K) = (Nat.card H : K) * a.coeff 1 := by
  intro K H _ _ _ _ a ha
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hi : IsIdempotentElem (LinearMap.mulLeft K a) := by
    change LinearMap.mulLeft K a * LinearMap.mulLeft K a = LinearMap.mulLeft K a
    refine LinearMap.ext fun x => ?_
    change a * (a * x) = a * x
    rw [← mul_assoc, ha]
  rw [← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace]
  rw [LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis H K), Matrix.trace]
  have h : ∀ g : H, Matrix.diag (LinearMap.toMatrix (MonoidAlgebra.basis H K)
      (MonoidAlgebra.basis H K) (LinearMap.mulLeft K a)) g = a.coeff 1 := by
    intro g
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
      LinearMap.mulLeft_apply]
    change (a * MonoidAlgebra.single g 1).coeff g = a.coeff 1
    rw [MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]
  rw [Finset.sum_congr rfl (fun g _ => h g), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

end GlobalTheory.BadCount
