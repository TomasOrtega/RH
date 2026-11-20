import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankTwistedLeftInvariantMulOfFreeAction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFinrankTwistedLeftInvariantMulOfFreeAction.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) (m : ℕ), Γ.FiniteIndex → FiniteDimensional ℂ E → 0 < m → g ^ m = 1 → A ^ m = 1 → (∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ) → FiniteDimensional ℂ (twInv Γ g A) ∧ Module.finrank ℂ (twInv Γ g A) * m = Γ.index * Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free <;> assumption)
