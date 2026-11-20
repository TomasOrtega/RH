import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationMaximalIdealEqSpanNilpotentArtinian
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.localization_maximalIdeal_eq_span_of_nilpotent` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalizationMaximalIdealEqSpanNilpotentArtinian.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.localization_maximalIdeal_eq_span_nilpotent_artinian : ∀ (D : Type) [CommRing D] [IsArtinianRing D] (x : D), IsNilpotent x → IsReduced (D ⧸ Ideal.span {x}) → ∀ (P : Ideal D) [P.IsMaximal], IsLocalRing.maximalIdeal (Localization.AtPrime P) = Ideal.span {algebraMap D (Localization.AtPrime P) x} := by
  first | exact @GlobalTheory.localization_maximalIdeal_eq_span_of_nilpotent | exact GlobalTheory.localization_maximalIdeal_eq_span_of_nilpotent | (intros; apply GlobalTheory.localization_maximalIdeal_eq_span_of_nilpotent <;> assumption)
