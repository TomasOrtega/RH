import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSeparablePointOfSeparableClosurePoin
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteSeparablePointOfSeparableClosurePoin.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_finite_separable_point_of_separableClosure_point' : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → Nonempty (B →ₐ[k] SeparableClosure k) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  first | exact @GlobalTheory.exists_finite_separable_point_of_separableClosure_point | exact GlobalTheory.exists_finite_separable_point_of_separableClosure_point | (intros; apply GlobalTheory.exists_finite_separable_point_of_separableClosure_point <;> assumption)
