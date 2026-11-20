import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumLeAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Ram.jumpSum_le_add` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRamificationJumpSumLeAdd.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.ramificationJumpSum_le_add : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) → B ≤ A → jumpSum R A C ≤ jumpSum R A B + jumpSum R B C := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_le_add | exact GlobalTheory.PMon.Ram.jumpSum_le_add | (intros; apply GlobalTheory.PMon.Ram.jumpSum_le_add <;> assumption)
