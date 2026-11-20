import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassHasDivisorOfDegreeLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_hasDivisorOfDegree_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N a : ℕ, 0 < a → a < N → mass g N (HasDiv g a) ≤ 7 / 8 := by
  first | exact @GlobalTheory.BadShare.mass_hasDiv_le | exact GlobalTheory.BadShare.mass_hasDiv_le | (intros; apply GlobalTheory.BadShare.mass_hasDiv_le <;> assumption)
