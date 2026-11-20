import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAdicCompleteOfFgOfNatCastMem
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFormalGroupCharts%2FIsAdicCompleteOfFgOfNatCastMem.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (p : ℕ), p ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O → ∀ J : Ideal O, J.FG → J ≠ ⊤ → (p : O) ∈ J → IsAdicComplete J O := by
  first | exact @GlobalTheory.isAdicComplete_of_fg_of_natCast_mem | exact GlobalTheory.isAdicComplete_of_fg_of_natCast_mem | (intros; apply GlobalTheory.isAdicComplete_of_fg_of_natCast_mem <;> assumption)
