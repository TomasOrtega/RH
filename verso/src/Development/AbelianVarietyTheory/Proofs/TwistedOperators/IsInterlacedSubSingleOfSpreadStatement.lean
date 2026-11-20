import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsInterlacedSubSingleOfSpread
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepReal.interlaced_sub_single` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsInterlacedSubSingleOfSpread.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.isInterlaced_sub_single_of_spread : ∀ {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}, GlobalTheory.SepReal.Interlaced ε lam ε' mu → (∀ a c, a ≠ c → 2 ≤ |lam a - lam c|) → (∀ a i, mu i < lam a → mu i + 1 < lam a) → (∀ a i, lam a ≠ mu i) → ∀ s, GlobalTheory.SepReal.Interlaced ε (lam - Pi.single s 1) ε' mu := by
  first | exact @GlobalTheory.SepReal.interlaced_sub_single | exact GlobalTheory.SepReal.interlaced_sub_single | (intros; apply GlobalTheory.SepReal.interlaced_sub_single <;> assumption)
