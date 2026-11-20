import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsNormEqXModMonicOfAdicCompleteInvolution.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.exists_norm_eq_X_mod_monic_of_adicComplete_involution : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] (c : O →+* O), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) → ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X := by
  first | exact @GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X | exact GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X | (intros; apply GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X <;> assumption)
