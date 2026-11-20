import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLang
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FC1FiniteExtensionLang.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K],
  (∀ (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) F), (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0) → IsFirstChernClassOfLineBundle K := by
  first | exact @GlobalTheory.is_c1_of_finite_of_tsen_lang_systems | exact GlobalTheory.is_c1_of_finite_of_tsen_lang_systems | (intros; apply GlobalTheory.is_c1_of_finite_of_tsen_lang_systems <;> assumption)
