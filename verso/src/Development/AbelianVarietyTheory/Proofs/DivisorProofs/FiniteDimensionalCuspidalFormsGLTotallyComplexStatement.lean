import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspidalFormsGLTotallyComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteDimensionalCuspidalFormsGLTotallyComplex.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_cuspidalForms_GL_totallyComplex : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ V : Submodule ℂ (Sm E a), V ≤ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) → (∀ φ ∈ V, IsCuspidal φ.1) → FiniteDimensional ℂ V := by
  first | exact @GlobalTheory.HCF.finiteDimensional_cuspGL | exact GlobalTheory.HCF.finiteDimensional_cuspGL | (intros; apply GlobalTheory.HCF.finiteDimensional_cuspGL <;> assumption)
