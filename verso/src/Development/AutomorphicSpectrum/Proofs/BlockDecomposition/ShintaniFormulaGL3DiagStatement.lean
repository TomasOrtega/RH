import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShintaniFormulaGL3Diag
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FShintaniFormulaGL3Diag.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.shintani_formula_GL3_diag : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (z : Fin 3 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ z (dg (unifUnit F ^ a) (unifUnit F ^ b) 1) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * Spherical.evalAt z (Spherical.schur ![a, b, 0]) else 0 := by
  first | exact @GlobalTheory.CompanionTheory.SphGL3.sph_dg_zpow | exact GlobalTheory.CompanionTheory.SphGL3.sph_dg_zpow | (intros; apply GlobalTheory.CompanionTheory.SphGL3.sph_dg_zpow <;> assumption)
