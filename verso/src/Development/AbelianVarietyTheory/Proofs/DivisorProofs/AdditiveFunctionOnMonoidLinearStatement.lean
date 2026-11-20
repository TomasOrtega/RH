import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionOnMonoidLinear
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AddExt.exists_linear` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdditiveFunctionOnMonoidLinear.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.additive_function_on_monoid_linear : ∀ (ι : Type) [Fintype ι] (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ), (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) → ∃ κ : ι → ℝ, ∀ x ∈ S, c x = ∑ i, (x i : ℝ) * κ i := by
  first | exact @GlobalTheory.AddExt.exists_linear | exact GlobalTheory.AddExt.exists_linear | (intros; apply GlobalTheory.AddExt.exists_linear <;> assumption)
