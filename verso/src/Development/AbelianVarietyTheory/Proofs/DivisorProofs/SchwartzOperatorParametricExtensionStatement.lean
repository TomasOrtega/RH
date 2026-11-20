import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOperatorParametricExtension
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzOperatorParametricExtension.lean&line=245#L245)
-/
theorem _root_.GlobalTheory.T.schwartz_operator_parametric_extension : ∀ {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ), ∃ P : SchwartzMap (V × V') ℂ →L[ℂ] SchwartzMap (W × V') ℂ, ∀ (f : SchwartzMap (V × V') ℂ) (x' : V') (h : SchwartzMap V ℂ), (∀ x, h x = f (x, x')) → ∀ y, P f (y, x') = T h y := by
  first | exact @GlobalTheory.SchwartzFstOp.exists_tensorId | exact GlobalTheory.SchwartzFstOp.exists_tensorId | (intros; apply GlobalTheory.SchwartzFstOp.exists_tensorId <;> assumption)
