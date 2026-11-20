import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversionCoordinateLocalizationPolynomial
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsInversionCoordinateLocalizationPolynomial.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.exists_inversion_coordinate_localization_polynomial : ∀ (k : Type) [Field k] (P : Polynomial k), P ≠ 0 → ∃ Q : Polynomial k, Q ≠ 0 ∧ ∃ (σ : Localization.Away P →ₐ[k] Localization.Away Q) (τ : Localization.Away Q →ₐ[k] Localization.Away (Polynomial.X * P)), (τ.comp σ).toRingHom.comp (algebraMap (Polynomial k) (Localization.Away P)) = algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) ∧ τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q)) = (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P * IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  first | exact @GlobalTheory.localizationAway_inv_coordinate | exact GlobalTheory.localizationAway_inv_coordinate | (intros; apply GlobalTheory.localizationAway_inv_coordinate <;> assumption)
