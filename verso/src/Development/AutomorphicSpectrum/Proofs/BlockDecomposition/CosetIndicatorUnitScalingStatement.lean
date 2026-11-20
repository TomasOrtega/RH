import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetIndicatorUnitScaling
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
Apply `GlobalTheory.CompanionTheory.WS.cosetInd_unit_smul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCosetIndicatorUnitScaling.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.coset_indicator_unit_scaling : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F) (t : Fˣ), t ∈ unitFiltrationUnits F 0 → GlobalTheory.CompanionTheory.WS.cosetInd n ((t : F) • x) = fun v => GlobalTheory.CompanionTheory.WS.cosetInd n x (((t⁻¹ : Fˣ) : F) • v) := by
  first | exact @GlobalTheory.CompanionTheory.WS.cosetInd_unit_smul | exact GlobalTheory.CompanionTheory.WS.cosetInd_unit_smul | (intros; apply GlobalTheory.CompanionTheory.WS.cosetInd_unit_smul <;> assumption)
