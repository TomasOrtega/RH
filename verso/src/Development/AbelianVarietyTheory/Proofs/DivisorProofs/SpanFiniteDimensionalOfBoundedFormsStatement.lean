import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensionalOfBoundedForms
import Mathlib

open Topology Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.span_finiteDimensional_of_bounded_forms` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpanFiniteDimensionalOfBoundedForms.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s) := by
  first | exact @GlobalTheory.span_finiteDimensional_of_bounded_forms | exact GlobalTheory.span_finiteDimensional_of_bounded_forms | (intros; apply GlobalTheory.span_finiteDimensional_of_bounded_forms <;> assumption)
