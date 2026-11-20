import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorization
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FBlockLUFactorization.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.block_LU_factorization : ∀ (N j : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ G = L * U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper <;> assumption)
