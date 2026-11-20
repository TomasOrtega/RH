import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetIndicatorSchwartzBruhat
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCosetIndicatorSchwartzBruhat.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.coset_indicator_schwartz_bruhat : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.cosetInd n x) := by
  first | exact @GlobalTheory.CompanionTheory.WS.Coset.isSB_cosetInd | exact GlobalTheory.CompanionTheory.WS.Coset.isSB_cosetInd | (intros; apply GlobalTheory.CompanionTheory.WS.Coset.isSB_cosetInd <;> assumption)
