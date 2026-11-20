import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

namespace GlobalTheory

open Matrix Polynomial
open scoped BigOperators

/- English proof (translation)
Set `K` to `FractionRing o`. Use `letI : Algebra K Om := FractionRing.liftAlgebra o Om`. Use `haveI : Algebra.EssFiniteType o K := .of_isLocalization K (nonZeroDivisors o)`. Set `E` to `IntermediateField.adjoin K T`. Use `haveI : Algebra.EssFiniteType K E := IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite hT)`.

Establish `hle : Subfield.closure (Set.range (algebraMap o Om) ∪ T) ≤ E.toSubfield`. Use `Subfield.closure_le.mpr (Set.union_subset ?_ (IntermediateField.subset_adjoin K T))` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[IsScalarTower.algebraMap_apply o K Om]`. Conclude with `E.algebraMap_mem _`.

Use `letI : Algebra (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E := (Subfield.inclusion hle).toAlgebra`. Use `haveI : IsScalarTower (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E Om := .of_algebraMap_eq fun _ => rfl`. Use `haveI : Module.Finite E Om := .of_restrictScalars_finite (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E Om`. Use `haveI : Algebra.EssFiniteType K Om := .comp K E Om`. Conclude with `.comp o K Om`.
-/
theorem essFiniteType_of_finiteDimensional_subfield_closure {o Om : Type*} [CommRing o]
    [IsDomain o] [Field Om] [Algebra o Om] [FaithfulSMul o Om] {T : Set Om} (hT : T.Finite)
    (h : FiniteDimensional (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) Om) :
    Algebra.EssFiniteType o Om := by
  let K := FractionRing o
  letI : Algebra K Om := FractionRing.liftAlgebra o Om
  haveI : Algebra.EssFiniteType o K := .of_isLocalization K (nonZeroDivisors o)
  let E := IntermediateField.adjoin K T
  haveI : Algebra.EssFiniteType K E :=
    IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite hT)
  have hle : Subfield.closure (Set.range (algebraMap o Om) ∪ T) ≤ E.toSubfield := by
    refine Subfield.closure_le.mpr (Set.union_subset ?_ (IntermediateField.subset_adjoin K T))
    rintro _ ⟨x, rfl⟩
    rw [IsScalarTower.algebraMap_apply o K Om]
    exact E.algebraMap_mem _
  letI : Algebra (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E :=
    (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E Om :=
    .of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite E Om :=
    .of_restrictScalars_finite (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E Om
  haveI : Algebra.EssFiniteType K Om := .comp K E Om
  exact .comp o K Om

end GlobalTheory
