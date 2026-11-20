import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmodule
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.quotient_lattice_by_isotropic_submodule` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FQuotientLatticeByIsotropicSubmodule.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.quotient_lattice_by_isotropic_submodule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R.form I → ∃ (g' : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (R' : RiemLat E g' Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q ∧ LinearMap.ker q = Submodule.span ℂ (R.P '' I) ∧ (∀ a x, q (R.B a x) = R'.B a (q x)) ∧ Set.range R'.P = q '' (R.P '' {x | ∀ y ∈ I, R.form x y = 0}) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  first | exact @GlobalTheory.CompanionTheory.Relay.quotient_lattice_by_isotropic_submodule | exact GlobalTheory.CompanionTheory.Relay.quotient_lattice_by_isotropic_submodule | (intros; apply GlobalTheory.CompanionTheory.Relay.quotient_lattice_by_isotropic_submodule <;> assumption)
