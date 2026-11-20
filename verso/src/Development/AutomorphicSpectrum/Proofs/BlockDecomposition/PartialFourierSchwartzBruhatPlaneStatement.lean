import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierSchwartzBruhatPlane
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPartialFourierSchwartzBruhatPlane.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.partial_fourier_schwartz_bruhat_plane : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.pF χ Φ) := by
  first | exact @GlobalTheory.CompanionTheory.WS.PF.isSB_pF | exact GlobalTheory.CompanionTheory.WS.PF.isSB_pF | (intros; apply GlobalTheory.CompanionTheory.WS.PF.isSB_pF <;> assumption)
