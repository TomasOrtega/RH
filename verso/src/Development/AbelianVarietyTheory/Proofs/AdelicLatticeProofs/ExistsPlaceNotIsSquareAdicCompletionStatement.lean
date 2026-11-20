import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotIsSquareAdicCompletion
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsPlaceNotIsSquareAdicCompletion.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.exists_place_not_isSquare_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), u ≠ 0 → ¬ IsSquare u → ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  first | exact @GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion | exact GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion | (intros; apply GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion <;> assumption)
