import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanExtendScalarsInfEqBotOfInfEqBot
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FSpanExtendScalarsInfEqBotOfInfEqBot.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.span_extendScalars_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ → Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  first | exact @GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot | exact GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot | (intros; apply GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot <;> assumption)
