import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexUnitsSquareUnderRingHomAdicCompletionLe
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FIndexUnitsSquareUnderRingHomAdicCompletionLe.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  first | exact @GlobalTheory.QNorm.index_sqSub_adicCompletion_le | exact GlobalTheory.QNorm.index_sqSub_adicCompletion_le | (intros; apply GlobalTheory.QNorm.index_sqSub_adicCompletion_le <;> assumption)
