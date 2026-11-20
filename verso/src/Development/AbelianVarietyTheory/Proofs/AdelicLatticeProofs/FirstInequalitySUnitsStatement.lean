import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnits
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QNorm.first_inequality_sUnits` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FFirstInequalitySUnits.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.two_mul_relIndex_normSub_sUnits_le : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧ 2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ 2 ^ (tFin F δ S + tReal F δ) := by
  first | exact @GlobalTheory.QNorm.first_inequality_sUnits | exact GlobalTheory.QNorm.first_inequality_sUnits | (intros; apply GlobalTheory.QNorm.first_inequality_sUnits <;> assumption)
