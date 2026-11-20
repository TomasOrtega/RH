import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfLocalRetractionsModMaximalIdealPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatOfLocalRetractionsModMaximalIdealPow.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.flat_of_local_retractions_mod_maximalIdeal_pow : ∀ {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ], (∀ n : ℕ, ∃ ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1), ψ.comp φ = Ideal.Quotient.mk _) → (∀ n : ℕ, ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ → IsLocalHom g₂ → g₁.comp φ = g₂.comp φ → g₁ = g₂) → φ.Flat := by
  first | exact @GlobalTheory.flat_of_retractions_mod_pow | exact GlobalTheory.flat_of_retractions_mod_pow | (intros; apply GlobalTheory.flat_of_retractions_mod_pow <;> assumption)
