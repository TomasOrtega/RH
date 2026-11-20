import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open GlobalTheory.ArchSch
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTranslationInvariantFunctionalRestrict.lean&line=282#L282)
-/
theorem _root_.GlobalTheory.T.translation_invariant_functional_restrict : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (P : Submodule ℝ Y)
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, (∀ p ∈ P, L p = 0) → ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, (∀ p ∈ P, f p = g p) → ℓ f = ℓ g := by
  first | exact @GlobalTheory.SchwartzHadamard.eq_of_eqOn | exact GlobalTheory.SchwartzHadamard.eq_of_eqOn | (intros; apply GlobalTheory.SchwartzHadamard.eq_of_eqOn <;> assumption)
