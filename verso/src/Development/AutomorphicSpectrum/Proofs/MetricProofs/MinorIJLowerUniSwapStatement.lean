import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJLowerUniSwap
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FMinorIJLowerUniSwap.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.minorIJ_lowerUni_swap : ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (a b : Fin N), IsLowerUni X → a ∉ S → b ∈ S → b < a → (∀ c ∈ S, c ≠ b → X c b = 0) → minorIJ X (insert a (S.erase b)) S = pSgn S a b * X a b ∧ pSgn S a b ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead.minor_replace | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead.minor_replace | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead.minor_replace <;> assumption)
