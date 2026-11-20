import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteInvolutionFixedUnitEqMulConj

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finite_involution_fixed_unit_isNorm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FFiniteInvolutionFixedUnitEqMulConj.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.finite_involution_fixed_unit_eq_mul_conj : ∀ (S : Type) [CommRing S] [Finite S] (c : S →+* S), (∀ x, c (c x) = x) → (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  first | exact @GlobalTheory.finite_involution_fixed_unit_isNorm | exact GlobalTheory.finite_involution_fixed_unit_isNorm | (intros; apply GlobalTheory.finite_involution_fixed_unit_isNorm <;> assumption)
