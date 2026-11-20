import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCosetsUnitIdelesCompletedOrder
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMVal.Euler.exists_finset_cover_units` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteCosetsUnitIdelesCompletedOrder.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_finite_cosets_unitIdeles_completedOrder : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ → ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  first | exact @GlobalTheory.CMVal.Euler.exists_finset_cover_units | exact GlobalTheory.CMVal.Euler.exists_finset_cover_units | (intros; apply GlobalTheory.CMVal.Euler.exists_finset_cover_units <;> assumption)
