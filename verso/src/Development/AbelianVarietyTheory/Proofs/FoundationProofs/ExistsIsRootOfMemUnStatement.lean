import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsIsRootOfMemUn.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.exists_isRoot_of_mem_Un_of_jHol : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  first | exact @GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | exact GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | (intros; apply GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un <;> assumption)
