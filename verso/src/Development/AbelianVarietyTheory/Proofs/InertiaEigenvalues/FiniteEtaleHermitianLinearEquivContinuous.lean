import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

/- English proof (translation)
Use `haveI : LocallyCompactSpace F := Unram.lcF E`. Use `haveI : CompleteSpace F := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))`. Use `haveI : FiniteDimensional F (Fin r → E) := inferInstance`. Use `haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L`.

Use `haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `IsModuleTopology.continuous_of_linearMap (R := F) (j.toLinearMap.restrictScalars F)`. Conclude with `LinearMap.continuous_of_finiteDimensional (j.symm.toLinearMap.restrictScalars F)`.
-/
theorem et_equiv_continuous (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous j ∧ Continuous j.symm := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : CompleteSpace F := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  haveI : FiniteDimensional F (Fin r → E) := inferInstance
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  refine ⟨?_, ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap (R := F) (j.toLinearMap.restrictScalars F)
  · exact LinearMap.continuous_of_finiteDimensional (j.symm.toLinearMap.restrictScalars F)

end GlobalTheory.JR
