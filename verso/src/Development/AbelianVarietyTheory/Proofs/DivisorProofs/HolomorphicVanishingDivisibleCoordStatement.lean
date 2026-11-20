import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicVanishingDivisibleCoord
open scoped ContDiff Topology
open Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoordDivision.hadamard_coord` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHolomorphicVanishingDivisibleCoord.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.holomorphic_vanishing_divisible_coord : ∀ {e : ℕ} (h : (Fin e → ℂ) → ℂ) (z0 : Fin e → ℂ) (r : ℝ) (k : Fin e), 0 < r → z0 k = 0 → AnalyticOnNhd ℂ h (Metric.ball z0 r) → (∀ z ∈ Metric.ball z0 r, z k = 0 → h z = 0) → ∃ g : (Fin e → ℂ) → ℂ, ContDiffOn ℝ ∞ g (Metric.ball z0 r) ∧ g z0 = fderiv ℂ h z0 (Pi.single k 1) ∧ ∀ z ∈ Metric.ball z0 r, h z = z k * g z := by
  first | exact @GlobalTheory.CoordDivision.hadamard_coord | exact GlobalTheory.CoordDivision.hadamard_coord | (intros; apply GlobalTheory.CoordDivision.hadamard_coord <;> assumption)
