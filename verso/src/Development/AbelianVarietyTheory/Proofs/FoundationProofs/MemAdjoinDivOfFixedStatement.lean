import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemAdjoinDivOfFixed
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.mem_adjoin_div_of_fixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMemAdjoinDivOfFixed.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_div_mem_adjoin_of_fixed : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ (S : Set Ω) (x : Ω), (∀ g : Ω ≃ₐ[R] Ω, (∀ s ∈ S, g s = s) → g x = x) → ∃ b ∈ Algebra.adjoin R S, ∃ c ∈ Algebra.adjoin R S, c ≠ 0 ∧ x = b / c := by
  first | exact @GlobalTheory.mem_adjoin_div_of_fixed | exact GlobalTheory.mem_adjoin_div_of_fixed | (intros; apply GlobalTheory.mem_adjoin_div_of_fixed <;> assumption)
