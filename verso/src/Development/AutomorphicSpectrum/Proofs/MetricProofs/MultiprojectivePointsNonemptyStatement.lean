import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonempty
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FMultiprojectivePointsNonempty.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.multiprojective_points_nonempty : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, ι k) → Ω), (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → (mcPts (mCoordIdeal x)).Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty <;> assumption)
