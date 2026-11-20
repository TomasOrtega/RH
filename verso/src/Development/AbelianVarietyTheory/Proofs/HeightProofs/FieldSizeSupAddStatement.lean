import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAdd
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FieldSize.sz_sup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FFieldSizeSupAdd.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.field_size_sup_add : ∀ (F F' : IntermediateField ℚ ℂ) (a b a' b' : ℝ), Sz F a b → Sz F' a' b' → Sz (F ⊔ F') (a + a') (b + b') := by
  first | exact @GlobalTheory.FieldSize.sz_sup | exact GlobalTheory.FieldSize.sz_sup | (intros; apply GlobalTheory.FieldSize.sz_sup <;> assumption)
