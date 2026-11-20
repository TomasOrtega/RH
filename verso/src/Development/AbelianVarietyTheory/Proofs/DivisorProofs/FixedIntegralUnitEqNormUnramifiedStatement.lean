import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedIntegralUnitEqNormUnramified
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFixedIntegralUnitEqNormUnramified.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.fixed_integral_unit_eq_norm_unramified : ∀ (K : GlobalTheory.UnitLemma.UQ) (t : K.O), IsUnit t → K.c (algebraMap K.O K.E t) = algebraMap K.O K.E t →
    ∃ v : K.E, v * K.c v = algebraMap K.O K.E t := by
  first | exact @GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm | exact GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm | (intros; apply GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm <;> assumption)
