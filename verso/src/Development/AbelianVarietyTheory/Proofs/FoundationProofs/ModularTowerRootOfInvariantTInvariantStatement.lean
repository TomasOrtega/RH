import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TInv.sl_T_eq` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FModularTowerRootOfInvariantTInvariant.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.modularTower_rootOfInvariant_T_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l n : ℕ), l.Prime → l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ∀ (u : X.K), u ≠ 0 → Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (u ^ (l ^ n)) → (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) → ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (u * X.sl (ofSL δ) u) ^ (l ^ n) = g ^ (l ^ n)) → X.sl (ofSL ModularGroup.T) u = u := by
  first | exact @GlobalTheory.TInv.sl_T_eq | exact GlobalTheory.TInv.sl_T_eq | (intros; apply GlobalTheory.TInv.sl_T_eq <;> assumption)
