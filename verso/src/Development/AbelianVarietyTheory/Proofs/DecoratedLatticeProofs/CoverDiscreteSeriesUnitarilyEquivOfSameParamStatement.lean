import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoverDS.unitEquiv_of_dsUnique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FCoverDiscreteSeriesUnitarilyEquivOfSameParam.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.coverDiscreteSeriesUnitarilyEquiv_of_sameParam : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  first | exact @GlobalTheory.CoverDS.unitEquiv_of_dsUnique | exact GlobalTheory.CoverDS.unitEquiv_of_dsUnique | (intros; apply GlobalTheory.CoverDS.unitEquiv_of_dsUnique <;> assumption)
