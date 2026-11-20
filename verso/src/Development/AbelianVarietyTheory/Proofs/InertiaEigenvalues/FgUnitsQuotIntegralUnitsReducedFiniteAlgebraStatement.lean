import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsReducedFiniteAlgebra
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFgUnitsQuotIntegralUnitsReducedFiniteAlgebra.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) → ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A] [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by
  first | exact @GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg | exact GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg | (intros; apply GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg <;> assumption)
