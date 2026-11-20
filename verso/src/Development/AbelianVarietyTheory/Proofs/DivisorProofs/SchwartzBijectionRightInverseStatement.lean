import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzBijectionRightInverse.lean&line=210#L210)
-/
theorem _root_.GlobalTheory.T.schwartz_bijection_right_inverse : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ), Function.Bijective T → ∃ S : SchwartzMap W ℂ →L[ℂ] SchwartzMap V ℂ, ∀ f, T (S f) = f := by
  first | exact @GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse | exact GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse | (intros; apply GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse <;> assumption)
