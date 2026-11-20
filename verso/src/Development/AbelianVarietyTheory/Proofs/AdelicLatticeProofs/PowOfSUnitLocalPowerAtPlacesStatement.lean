import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowOfSUnitLocalPowerAtPlaces
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FPowOfSUnitLocalPowerAtPlaces.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.pow_of_sUnit_localPower_at_places : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (ζ : F) (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ → ∀ y ∈ sUnits F (S ∪ T), y ∈ finPow p F S → ∃ r : F, r ^ p = (y : F) := by
  first | exact @GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow | exact GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow | (intros; apply GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow <;> assumption)
