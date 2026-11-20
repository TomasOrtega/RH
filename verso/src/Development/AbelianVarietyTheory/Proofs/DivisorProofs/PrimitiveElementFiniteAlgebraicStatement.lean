import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveElementFiniteAlgebraic
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.exists_primitive_element_of_isAlgebraic_fin | exact GlobalTheory.exists_primitive_element_of_isAlgebraic_fin | (intros; apply GlobalTheory.exists_primitive_element_of_isAlgebraic_fin <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.primitive_element_finite_algebraic : ∀ (K C : Type) [Field K] [CharZero K] [Field C] [Algebra K C] (m : ℕ) (a : Fin m → C), (∀ j, IsAlgebraic K (a j)) → ∃ α : C, IsAlgebraic K α ∧ ∀ j, a j ∈ IntermediateField.adjoin K {α} := by
  first | exact @GlobalTheory.exists_primitive_element_of_isAlgebraic_fin | exact GlobalTheory.exists_primitive_element_of_isAlgebraic_fin | (intros; apply GlobalTheory.exists_primitive_element_of_isAlgebraic_fin <;> assumption)
