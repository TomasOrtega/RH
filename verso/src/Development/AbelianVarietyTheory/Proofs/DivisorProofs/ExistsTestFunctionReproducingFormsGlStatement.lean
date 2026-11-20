import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingFormsGl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsTestFunctionReproducingFormsGl.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.exists_test_function_reproducing_forms_gl : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ β : Lie E a → ℂ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ invSet E a ∧ ∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  first | exact @GlobalTheory.HCSmoothGL.exists_smooth_beta | exact GlobalTheory.HCSmoothGL.exists_smooth_beta | (intros; apply GlobalTheory.HCSmoothGL.exists_smooth_beta <;> assumption)
