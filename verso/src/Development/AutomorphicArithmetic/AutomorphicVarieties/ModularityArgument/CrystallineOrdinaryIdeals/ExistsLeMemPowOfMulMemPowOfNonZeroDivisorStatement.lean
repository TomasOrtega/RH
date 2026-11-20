import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsLeMemPowOfMulMemPowOfNonZeroDivisor
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FAutomorphicVarieties%2FModularityArgument%2FCrystallineOrdinaryIdeals%2FExistsLeMemPowOfMulMemPowOfNonZeroDivisor.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_le_mem_pow_of_mul_mem_pow_of_nonZeroDivisor : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (m : Ideal A) (δ : A), (∀ a, δ * a = 0 → a = 0) → ∀ j : ℕ, ∃ k : ℕ, j ≤ k ∧ ∀ a, δ * a ∈ m ^ k → a ∈ m ^ j := by
  first | exact @GlobalTheory.exists_pow_mem_of_mul_mem_pow | exact GlobalTheory.exists_pow_mem_of_mul_mem_pow | (intros; apply GlobalTheory.exists_pow_mem_of_mul_mem_pow <;> assumption)
