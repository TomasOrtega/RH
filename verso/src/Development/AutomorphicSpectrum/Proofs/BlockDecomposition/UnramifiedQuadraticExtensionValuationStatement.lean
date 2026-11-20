import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticExtensionValuation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedQuadraticExtensionValuation.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.unramified_quadratic_extension_valuation : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → residueCard E = residueCard F ^ 2 → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SphTheta.UnramQuad.ord_unifUnit_of_residueCard_eq_sq | exact GlobalTheory.CompanionTheory.SphTheta.UnramQuad.ord_unifUnit_of_residueCard_eq_sq | (intros; apply GlobalTheory.CompanionTheory.SphTheta.UnramQuad.ord_unifUnit_of_residueCard_eq_sq <;> assumption)
