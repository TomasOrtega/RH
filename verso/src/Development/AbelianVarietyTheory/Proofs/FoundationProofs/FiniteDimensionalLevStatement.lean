import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLev
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K4.finiteDimensional_lev` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFiniteDimensionalLev.lean&line=312#L312)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_lev_of_gamma_le : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ' → letI := GlobalTheory.K4.algRat X Γ'; FiniteDimensional (RatFunc Ω) (GlobalTheory.K4.lev X Γ') := by
  first | exact @GlobalTheory.K4.finiteDimensional_lev | exact GlobalTheory.K4.finiteDimensional_lev | (intros; apply GlobalTheory.K4.finiteDimensional_lev <;> assumption)
