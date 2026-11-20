import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsPrimeDegree
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FFirstInequalitySUnitsPrimeDegree.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.first_inequality_sUnits_prime_degree : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧ p * (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ p ^ tNon p F δ S := by
  first | exact @GlobalTheory.CNorm.first_inequality_sUnits_prime | exact GlobalTheory.CNorm.first_inequality_sUnits_prime | (intros; apply GlobalTheory.CNorm.first_inequality_sUnits_prime <;> assumption)
