import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedA
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedA.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified' : ∀ (P D : Type) [CommRing P] [IsDomain P] [CommRing D] [IsDomain D] [Algebra P D] [Algebra.FiniteType P D] [Algebra.FormallyUnramified P D] (f : D), f ≠ 0 → ∃ Q : P, Q ≠ 0 ∧ ∃ d : D, algebraMap P D Q = f * d := by
  first | exact @GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified | exact GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified | (intros; apply GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified <;> assumption)
