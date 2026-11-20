import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlocksParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.inductionFiniteLength_of_standard` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeviBlocksParabolicInductionFiniteLength.lean&line=253#L253)
-/
theorem _root_.GlobalTheory.T.induction_finite_length : GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionFiniteLength k := by
  first | exact @GlobalTheory.inductionFiniteLength_of_standard | exact GlobalTheory.inductionFiniteLength_of_standard | (intros; apply GlobalTheory.inductionFiniteLength_of_standard <;> assumption)
