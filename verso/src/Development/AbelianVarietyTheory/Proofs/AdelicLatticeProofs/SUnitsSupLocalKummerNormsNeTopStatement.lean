import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupLocalKummerNormsNeTop
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FSUnitsSupLocalKummerNormsNeTop.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → sUnits F S ⊔ finNorm p F δ S ≠ ⊤ := by
  first | exact @GlobalTheory.CNorm.sUnits_sup_finNorm_ne_top | exact GlobalTheory.CNorm.sUnits_sup_finNorm_ne_top | (intros; apply GlobalTheory.CNorm.sUnits_sup_finNorm_ne_top <;> assumption)
