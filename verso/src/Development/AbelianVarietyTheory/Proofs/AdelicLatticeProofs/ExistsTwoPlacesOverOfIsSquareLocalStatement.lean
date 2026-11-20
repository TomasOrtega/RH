import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocal
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QNorm.two_places_of_isSquare` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsTwoPlacesOverOfIsSquareLocal.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.exists_two_places_over_of_isSquare_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) δ) → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  first | exact @GlobalTheory.QNorm.two_places_of_isSquare | exact GlobalTheory.QNorm.two_places_of_isSquare | (intros; apply GlobalTheory.QNorm.two_places_of_isSquare <;> assumption)
