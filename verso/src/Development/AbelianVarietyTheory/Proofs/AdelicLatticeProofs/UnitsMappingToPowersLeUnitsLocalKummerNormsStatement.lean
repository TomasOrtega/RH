import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNorms
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FUnitsMappingToPowersLeUnitsLocalKummerNorms.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms : ∀ (p : ℕ), 0 < p → (∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), powSub p φ ≤ kNorm p φ δ) ∧ ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), kNorm p (RingHom.id F) δ ≤ kNorm p φ δ := by
  first | exact @GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map | exact GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map | (intros; apply GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map <;> assumption)
