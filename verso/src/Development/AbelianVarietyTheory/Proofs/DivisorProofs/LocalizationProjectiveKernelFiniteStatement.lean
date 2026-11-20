import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationProjectiveKernelFinite
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalizationProjectiveKernelFinite.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.localization_projective_kernel_finite : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M],
  Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) →
  ∀ (n : ℕ) (π : (Fin n → A) →ₗ[A] M), Function.Surjective π →
  Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) (LinearMap.ker π)) := by
  first | exact @GlobalTheory.finite_localized_ker_of_projective_away | exact GlobalTheory.finite_localized_ker_of_projective_away | (intros; apply GlobalTheory.finite_localized_ker_of_projective_away <;> assumption)
