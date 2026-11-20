import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetSeparatingFiniteDimensionalFunctions
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finiteDim_functions_detected_by_finset` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFinsetSeparatingFiniteDimensionalFunctions.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_finset_separating_finiteDimensional_functions : ∀ (K : Type) (W : Submodule ℂ (K → ℂ)), FiniteDimensional ℂ W → ∃ s : Finset K, ∀ w ∈ W, (∀ k ∈ s, w k = 0) → w = 0 := by
  first | exact @GlobalTheory.finiteDim_functions_detected_by_finset | exact GlobalTheory.finiteDim_functions_detected_by_finset | (intros; apply GlobalTheory.finiteDim_functions_detected_by_finset <;> assumption)
