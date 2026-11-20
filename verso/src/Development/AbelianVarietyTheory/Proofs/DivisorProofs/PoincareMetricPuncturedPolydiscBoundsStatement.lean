import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricPuncturedPolydiscBounds
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PoincareBounds.poincare_bounds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPoincareMetricPuncturedPolydiscBounds.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.poincareMetric_punctured_polydisc_bounds : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 → ∀ z ∈ punctured ha ρ, (poincareGram a z).PosSemidef ∧ ∀ ξ : Fin n → ℂ, (∀ k, ‖ξ k‖ ≤ 2 * gnorm (poincareGram a z) ξ) ∧ ∀ i : Fin a, ‖ξ (Fin.castLE ha i)‖ ≤ 2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) * gnorm (poincareGram a z) ξ := by
  first | exact @GlobalTheory.PoincareBounds.poincare_bounds | exact GlobalTheory.PoincareBounds.poincare_bounds | (intros; apply GlobalTheory.PoincareBounds.poincare_bounds <;> assumption)
