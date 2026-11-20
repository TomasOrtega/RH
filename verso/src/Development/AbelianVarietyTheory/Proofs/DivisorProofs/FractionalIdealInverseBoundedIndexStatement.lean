import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealInverseBoundedIndex
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_principal_mul_integral_ideal_contains_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFractionalIdealInverseBoundedIndex.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.fractional_ideal_inverse_bounded_index : ∀ (A K : Type) [CommRing A] [IsDomain A] [CharZero A] [Module.Finite ℤ A]
    [Field K] [Algebra A K] [IsFractionRing A K],
    ∃ M : ℤ, M ≠ 0 ∧ ∀ I J : Submodule A K, I * J = 1 →
      ∃ x : K, x ≠ 0 ∧ Submodule.span A {x} * I ≤ 1 ∧ (M : K) ∈ Submodule.span A {x} * I := by
  first | exact @GlobalTheory.exists_principal_mul_integral_ideal_contains_int | exact GlobalTheory.exists_principal_mul_integral_ideal_contains_int | (intros; apply GlobalTheory.exists_principal_mul_integral_ideal_contains_int <;> assumption)
