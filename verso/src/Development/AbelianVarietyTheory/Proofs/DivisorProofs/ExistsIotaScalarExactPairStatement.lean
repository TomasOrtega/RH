import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIotaScalarExactPair
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetInv.ScalarEx.exists_iotaScalar` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIotaScalarExactPair.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.exists_iota_scalar_exact_pair : ∀ (C : Type) [Field C] (N : ℕ) (α β : Matrix (Fin N) (Fin N) C), α * β = 0 → β * α = 0 → (∀ x, α *ᵥ x = 0 → ∃ y, x = β *ᵥ y) → ∃ lam : C, lam ≠ 0 ∧ IotaScalar α β β.rank lam := by
  first | exact @GlobalTheory.DetInv.ScalarEx.exists_iotaScalar | exact GlobalTheory.DetInv.ScalarEx.exists_iotaScalar | (intros; apply GlobalTheory.DetInv.ScalarEx.exists_iotaScalar <;> assumption)
