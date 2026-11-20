import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirst
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FFlagCoverArithmeticFirst.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.flag_cover_arithmetic_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), f z' ∈ mcPts (mCoordIdeal y) ∧ CovMap.IsImg Cv z' (f z') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img <;> assumption)
