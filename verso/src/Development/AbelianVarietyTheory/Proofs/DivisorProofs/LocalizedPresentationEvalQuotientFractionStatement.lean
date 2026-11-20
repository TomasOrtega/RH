import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedPresentationEvalQuotientFraction
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalizedPresentationEvalQuotientFraction.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.localized_presentation_eval_quotient_fraction : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (J : Ideal R) (n : ℕ), (∀ x ∈ J ^ n, c x = 0) → ∀ (m : ℕ) (r : Fin m → B), (∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q - MvPolynomial.eval₂ c r P ∈ Ideal.map c J) → ∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q = MvPolynomial.eval₂ c r P := by
  first | exact @GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent | exact GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent | (intros; apply GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent <;> assumption)
