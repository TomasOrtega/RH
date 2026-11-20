import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialIdealEqBotOfPderivStableNoConstants
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMvPolynomialIdealEqBotOfPderivStableNoConstants.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.mvPolynomial_ideal_eq_bot_of_pderiv_stable_no_constants : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by
  first | exact @GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable | exact GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable | (intros; apply GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable <;> assumption)
