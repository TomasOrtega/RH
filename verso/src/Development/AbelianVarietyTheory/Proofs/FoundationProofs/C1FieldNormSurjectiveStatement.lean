import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.norm_surjective_of_is_c1` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FC1FieldNormSurjective.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], IsFirstChernClassOfLineBundle K →
  ∀ b : K, b ≠ 0 → ∃ x : L, Algebra.norm K x = b := by
  first | exact @GlobalTheory.norm_surjective_of_is_c1 | exact GlobalTheory.norm_surjective_of_is_c1 | (intros; apply GlobalTheory.norm_surjective_of_is_c1 <;> assumption)
