import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSqEqOneOfFiniteAlgebra
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteSqEqOneOfFiniteAlgebra.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero : ∀ (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Set.Finite {x : A | x ^ 2 = 1} := by
  first | exact @GlobalTheory.finite_sq_eq_one_of_finite_algebra | exact GlobalTheory.finite_sq_eq_one_of_finite_algebra | (intros; apply GlobalTheory.finite_sq_eq_one_of_finite_algebra <;> assumption)
