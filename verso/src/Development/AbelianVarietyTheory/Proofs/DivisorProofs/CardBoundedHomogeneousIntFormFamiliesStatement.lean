import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBoundedHomogeneousIntFormFamilies
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardBoundedHomogeneousIntFormFamilies.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.card_bounded_homogeneous_int_form_families : ∀ (D q δ : ℕ) (R : ℝ), 0 ≤ R → {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R}.Finite ∧ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R}.ncard = (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ∧ Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D ∧ Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) = (q + D).choose D ∧ Module.Finite ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) := by
  first | exact @GlobalTheory.HSAmp.card_bounded_forms | exact GlobalTheory.HSAmp.card_bounded_forms | (intros; apply GlobalTheory.HSAmp.card_bounded_forms <;> assumption)
