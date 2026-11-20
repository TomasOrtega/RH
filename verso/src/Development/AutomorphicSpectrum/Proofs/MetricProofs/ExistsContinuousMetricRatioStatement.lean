import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousMetricRatio
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FExistsContinuousMetricRatio.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.exists_continuous_metric_ratio : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb : HermLine J), IsSmoothHerm Nb → Nb.a = muTwDeg Hd B → ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), κ (M.proj z) = Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Descent.logDiff_descends | exact GlobalTheory.CompanionTheory.Ar.Cusp.Descent.logDiff_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Descent.logDiff_descends <;> assumption)
