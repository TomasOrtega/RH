import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexOneUnitsMulEqCardQuotient
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FRelIndexOneUnitsMulEqCardQuotient.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.relIndex_oneUnits_mul_eq_card_quotient' : ∀ (O : Type) [CommRing O] [IsDomain O] (t s : O), t ≠ 0 → s ∣ t → Ideal.span {t} ≤ Ideal.jacobson (⊥ : Ideal O) → (oneUnits (s * t)).relIndex (oneUnits t) = Nat.card (O ⧸ Ideal.span {s}) := by
  first | exact @GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient | exact GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient | (intros; apply GlobalTheory.CNorm.relIndex_oneUnits_mul_eq_card_quotient <;> assumption)
