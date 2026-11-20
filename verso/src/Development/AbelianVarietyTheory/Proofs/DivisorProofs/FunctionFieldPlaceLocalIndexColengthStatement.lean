import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexColength
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Nef.local_index` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFunctionFieldPlaceLocalIndexColength.lean&line=173#L173)
-/
theorem _root_.GlobalTheory.T.functionFieldPlace_local_index_colength : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (h : Matrix (Fin n) (Fin n) F), h.det ≠ 0 → (∀ i j, v.1 (h⁻¹ i j) ≤ 1) → ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = -ord v h.det ∧ ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 → ∀ i, v.1 (h.mulVec x i) ≤ 1 := by
  first | exact @GlobalTheory.Nef.local_index | exact GlobalTheory.Nef.local_index | (intros; apply GlobalTheory.Nef.local_index <;> assumption)
