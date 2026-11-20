import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotientEqOfPowSubSelfMem
import Mathlib
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardQuotientEqOfPowSubSelfMem.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.card_quotient_eq_of_pow_sub_self_mem' : ∀ {R : Type} [CommRing R] (P : Ideal R) [P.IsMaximal] (q : ℕ) (ζ : R), 2 ≤ q → ζ ^ (q - 1) = 1 →
    (∀ j : ℕ, 0 < j → j < q - 1 → ζ ^ j - 1 ∉ P) → (∀ y : R, y ^ q - y ∈ P) → Nat.card (R ⧸ P) = q := by
  first | exact @GlobalTheory.card_quotient_eq_of_pow_sub_self_mem | exact GlobalTheory.card_quotient_eq_of_pow_sub_self_mem | (intros; apply GlobalTheory.card_quotient_eq_of_pow_sub_self_mem <;> assumption)
