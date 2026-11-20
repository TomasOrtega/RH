import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import GroundTheory.AutomorphicForms.ReductionMeasure
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdeleModule

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem distribHaarChar_principal : ∀ (F : Type) [Field F] [NumberField F]
    [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (a : Fˣ),
    distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) = 1 := by
  intro F _ _ _ _ a
  have : (GroundTheory.Global.adeleMeasure F).Regular := by
    obtain ⟨K⟩ := (inferInstance :
      Nonempty (TopologicalSpace.PositiveCompacts (AdeleRing (𝓞 F) F)))
    exact Measure.regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty
      K.isCompact.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := GroundTheory.Global.adeleMeasure F)
    (s := GroundTheory.Global.fundamentalSet F) ?_ ?_ ?_
  · rw [GroundTheory.Global.adeleMeasure_fundamentalSet]; exact one_ne_zero
  · rw [GroundTheory.Global.adeleMeasure_fundamentalSet]; exact ENNReal.one_ne_top
  · have h := GroundTheory.Global.adeleMeasure_smul (K := F) (GroundTheory.Global.IdeleGroup.diagonal F a)
      (GroundTheory.Global.fundamentalSet F)
    rw [GroundTheory.Global.IdeleGroup.ideleModule_diagonal] at h
    rw [ENNReal.coe_one]
    simpa using! h

end GlobalTheory.CompanionTheory.AdeleModule
