import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntRingHomContinuousOfPadicCoeff
import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPadicIntRingHomContinuousOfPadicCoeff.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.padicInt_ringHom_continuous_of_padicCoeff' : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → ∀ φ : ℤ_[p] →+* O, Continuous φ := by
  first | exact @GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff | exact GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff | (intros; apply GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff <;> assumption)
