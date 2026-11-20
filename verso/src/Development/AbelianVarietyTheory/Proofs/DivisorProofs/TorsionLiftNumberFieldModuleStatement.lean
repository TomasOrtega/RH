import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftNumberFieldModule
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.nsmul_surj_of_card_torsion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorsionLiftNumberFieldModule.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.torsion_lift_number_field_module : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F)) →
    ∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  first | exact @GlobalTheory.nsmul_surj_of_card_torsion | exact GlobalTheory.nsmul_surj_of_card_torsion | (intros; apply GlobalTheory.nsmul_surj_of_card_torsion <;> assumption)
