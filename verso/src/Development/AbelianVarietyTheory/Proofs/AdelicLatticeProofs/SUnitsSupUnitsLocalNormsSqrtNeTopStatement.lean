import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTop
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FSUnitsSupUnitsLocalNormsSqrtNeTop.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → sUnits F S ⊔ locNorm F δ S ≠ ⊤ := by
  first | exact @GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top | exact GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top | (intros; apply GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top <;> assumption)
