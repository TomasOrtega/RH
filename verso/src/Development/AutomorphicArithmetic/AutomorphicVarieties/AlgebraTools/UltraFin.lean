import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.ultra_fin :
    ∀ (ι Z : Type) (U : Ultrafilter ι) (a : ι → Z) (s : Set Z), s.Finite → (∀ᶠ i in (U : Filter ι), a i ∈ s) →
      ∃! z, z ∈ s ∧ ∀ᶠ i in (U : Filter ι), a i = z := by
  intro ι Z U a s hs h
  have hsub : {i | a i ∈ s} ⊆ ⋃ z ∈ s, {i | a i = z} := by
    intro i hi
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨a i, hi, rfl⟩
  have hmem : (⋃ z ∈ s, {i | a i = z}) ∈ U := U.1.sets_of_superset h hsub
  obtain ⟨z, hz, hzU⟩ := (Ultrafilter.finite_biUnion_mem_iff hs).1 hmem
  refine ⟨z, ⟨hz, hzU⟩, ?_⟩
  rintro w ⟨-, hw⟩
  obtain ⟨i, hi1, hi2⟩ := (hw.and hzU).exists
  exact hi1.symm.trans hi2
