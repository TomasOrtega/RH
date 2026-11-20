import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexUnitsOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FSubgroupPowRelIndexUnitsOfIsAdicComplete.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.subgroupPowRelIndex_units_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by
  first | exact @GlobalTheory.CNorm.pIdx_units_of_isAdicComplete | exact GlobalTheory.CNorm.pIdx_units_of_isAdicComplete | (intros; apply GlobalTheory.CNorm.pIdx_units_of_isAdicComplete <;> assumption)
