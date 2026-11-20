import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzSeminormTranslateSubLineDerivLe.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.schwartz_seminorm_translate_sub_lineDeriv_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f) ≤ C * t ^ 2 := by
  first | exact @GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le | exact GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le | (intros; apply GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le <;> assumption)
