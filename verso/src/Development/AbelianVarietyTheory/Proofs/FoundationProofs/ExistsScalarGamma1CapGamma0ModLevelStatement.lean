import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsScalarGamma1CapGamma0ModLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsScalarGamma1CapGamma0ModLevel.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_scalar_gamma1CapGamma0_mod_level : ∀ (N l a M : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → 0 < M → ¬ l ∣ M → ∃ c ∈ Gam N l, (∀ g : SL(2, ℤ), c * g * c⁻¹ * g⁻¹ ∈ CongruenceSubgroup.Gamma (M * N * l ^ a)) ∧ ∀ i j, (((c : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (l ^ a)) = if i = j then -1 else 0 := by
  first | exact @GlobalTheory.KZ.exists_scalar_mod_level | exact GlobalTheory.KZ.exists_scalar_mod_level | (intros; apply GlobalTheory.KZ.exists_scalar_mod_level <;> assumption)
