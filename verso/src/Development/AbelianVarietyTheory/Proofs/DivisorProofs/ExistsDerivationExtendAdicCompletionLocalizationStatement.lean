import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalization
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.derivation_extend_completion_localization_atPrime` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDerivationExtendAdicCompletionLocalization.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_derivation_extend_adicCompletion_localization : ∀ (S : Type) [CommRing S] (P : Ideal S) [P.IsPrime] (d : Derivation ℤ S S), ∃ D : Derivation ℤ (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)) (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)), ∀ x, D (algebraMap S _ x) = algebraMap S _ (d x) := by
  first | exact @GlobalTheory.derivation_extend_completion_localization_atPrime | exact GlobalTheory.derivation_extend_completion_localization_atPrime | (intros; apply GlobalTheory.derivation_extend_completion_localization_atPrime <;> assumption)
