import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPolynomialSubringMaximalIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_polySubring_maximal_integral` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsPolynomialSubringMaximalIntegral.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_polynomialSubring_maximal_integral : ∀ (k K : Type) [Field k] [Field K] (φ : k →+* K), ∃ (D : Subring K) (m₀ : Ideal D), φ.range ≤ D ∧ m₀.IsMaximal ∧
    (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) ∧ ∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x) := by
  first | exact @GlobalTheory.exists_polySubring_maximal_integral | exact GlobalTheory.exists_polySubring_maximal_integral | (intros; apply GlobalTheory.exists_polySubring_maximal_integral <;> assumption)
