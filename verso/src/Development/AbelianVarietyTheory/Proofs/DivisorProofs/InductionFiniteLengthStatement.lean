import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInductionFiniteLength.lean&line=193#L193)
-/
theorem _root_.GlobalTheory.T.jacquet_finite_length : GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  first | exact @GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard | exact GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard | (intros; apply GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard <;> assumption)
