import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscRatioGrowth
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FHolomorphicDiscRatioGrowth.lean&line=152#L152)
-/
theorem _root_.GlobalTheory.T.holomorphic_disc_ratio_growth : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc | exact GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc <;> assumption)
