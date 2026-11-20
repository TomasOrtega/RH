import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseCompactSupportSchwartz
import Mathlib
open SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDenseCompactSupportSchwartz.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.dense_compact_support_schwartz : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Dense {φ : SchwartzMap V ℂ | HasCompactSupport (⇑φ)} := by
  first | exact @GlobalTheory.dense_hasCompactSupport_schwartz | exact GlobalTheory.dense_hasCompactSupport_schwartz | (intros; apply GlobalTheory.dense_hasCompactSupport_schwartz <;> assumption)
