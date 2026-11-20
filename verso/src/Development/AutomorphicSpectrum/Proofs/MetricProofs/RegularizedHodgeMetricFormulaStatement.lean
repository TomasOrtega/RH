import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricFormula
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FRegularizedHodgeMetricFormula.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.regularized_hodge_metric_formula : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ), ∀ z ∈ mcPts (mCoordIdeal D.y), (muReg X.H X.S B t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts <;> assumption)
