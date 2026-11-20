import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantSchwartzUnique
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTranslationInvariantSchwartzUnique.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.translation_invariant_schwartz_unique : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (μ μ' : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ g = μ f) →
    (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ' g = μ' f) →
    μ ≠ 0 → ∃ c : ℂ, μ' = c • μ := by
  first | exact @GlobalTheory.TransInvSchwartz.dim_le_one | exact GlobalTheory.TransInvSchwartz.dim_le_one | (intros; apply GlobalTheory.TransInvSchwartz.dim_le_one <;> assumption)
