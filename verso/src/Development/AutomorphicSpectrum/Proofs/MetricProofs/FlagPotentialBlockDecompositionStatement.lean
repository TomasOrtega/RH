import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FFlagPotentialBlockDecomposition.lean&line=190#L190)
-/
theorem _root_.GlobalTheory.T.flag_potential_block_decomposition : ∀ (N j : ℕ) (i : Fin N) (Pi G h : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsPeriodGram j Pi G → IsBlockDiag j G → G.PosDef → IsBlockDiag j h → h.det ≠ 0 → InFlagDomain N j (Pi * h) ∧ stepPot N j i (Pi * h) = blockPot j i G h + Real.log ‖detFac j i h‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot | exact GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot <;> assumption)
