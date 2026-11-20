import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDual
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open ReciprocityTheory.PGsh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameDual.frameDual` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrameDual.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.exists_integral_dual_frame_of_isSatFrame : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (i d : ℕ) (u : Fin i → Fin d → C), IsSatFrame v u → ∃ l : Fin i → Fin d → C, (∀ a e, IsIntV v (l a e)) ∧ ∀ a a', ∑ e, l a e * u a' e = if a = a' then 1 else 0 := by
  first | exact @GlobalTheory.FrameDual.frameDual | exact GlobalTheory.FrameDual.frameDual | (intros; apply GlobalTheory.FrameDual.frameDual <;> assumption)
