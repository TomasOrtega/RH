import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableTwistedSectionLine
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegrableTwistedSectionLine.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.integrable_twisted_section_line : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Ψ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ u : Fˣ, Integrable (fun y : F => Ψ ((u : F), (u : F) * y) * (χ (-y) : ℂ)) (selfDualMeasure χ) := by
  first | exact @GlobalTheory.CompanionTheory.WS.inner_integrable | exact GlobalTheory.CompanionTheory.WS.inner_integrable | (intros; apply GlobalTheory.CompanionTheory.WS.inner_integrable <;> assumption)
