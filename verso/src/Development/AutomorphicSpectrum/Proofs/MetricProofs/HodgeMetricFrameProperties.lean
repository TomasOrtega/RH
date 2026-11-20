import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.MuFrameNormLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `LevelTowerAlt.mu_frame_norm_line` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FPlurisubharmonicCones%2FMuFrameNormLine.lean&line=239#L239)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_metric_frame_properties : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D), (∀ z ∈ mcPts (mCoordIdeal D.y), Nonempty (MuFrameAt Hd z)) ∧ (∀ z ∈ D.Xo, ∀ d : MuFrameAt Hd z, 0 < d.norm ∧ (muLine Hd).h z = d.norm) ∧ LogHom D Hd.aMu (phMu Hd) ∧ ConjOff D (phMu Hd) := by
  first | exact @LevelTowerAlt.mu_frame_norm_line | exact LevelTowerAlt.mu_frame_norm_line
