import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealBasisFromLatticeBasis
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FRealBasisFromLatticeBasis.lean&line=147#L147)
-/
theorem _root_.GlobalTheory.T.real_basis_from_lattice_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g N : ℕ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → g = Fintype.card Ψ * N → ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin N → E)), (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ lam : Module.Basis (Fin (2 * g)) ℤ Λ, ∃ bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin N → ℂ), ∀ k τ i, bas k τ i = embOf (σ τ) (e (lam k) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.exists_realBasis_of_latBasis | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.exists_realBasis_of_latBasis | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.exists_realBasis_of_latBasis <;> assumption)
