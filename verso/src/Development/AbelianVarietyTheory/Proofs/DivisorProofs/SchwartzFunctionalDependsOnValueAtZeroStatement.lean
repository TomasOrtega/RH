import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalDependsOnValueAtZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzFunctionalDependsOnValueAtZero.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.schwartz_functional_depends_on_value_at_zero : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => GlobalTheory.ArchSch.ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, f 0 = g 0 → ℓ f = ℓ g := by
  first | exact @GlobalTheory.CharInvAtZero.eq_of_eq_zero | exact GlobalTheory.CharInvAtZero.eq_of_eq_zero | (intros; apply GlobalTheory.CharInvAtZero.eq_of_eq_zero <;> assumption)
