import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionComplementEquiv
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FFlagDimensionComplementEquiv.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.flag_dimension_complement_equiv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ) (τ : Ψ) (ca cb : Fin N), j ≤ N → ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (Fin d ≃ Fin n ⊕ FC.CIdx Ψ N j τ ca cb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord.nonempty_equiv_cIdx | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord.nonempty_equiv_cIdx | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord.nonempty_equiv_cIdx <;> assumption)
