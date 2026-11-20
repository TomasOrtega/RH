import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInterOfFlatLinearlyDisjoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Desc.spanBy_image_inter` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpanImageInterOfFlatLinearlyDisjoint.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.span_image_inter_of_flat_linearlyDisjoint : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁), ρ.Flat → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (M N : Set F), (0 : F) ∈ M → (∀ a ∈ M, ∀ b ∈ M, a + b ∈ M) → (∀ r, ∀ a ∈ M, c₀ r * a ∈ M) → (0 : F) ∈ N → (∀ a ∈ N, ∀ b ∈ N, a + b ∈ N) → (∀ r, ∀ a ∈ N, c₀ r * a ∈ N) → spanBy c₁ (θ '' (M ∩ N)) = spanBy c₁ (θ '' M) ∩ spanBy c₁ (θ '' N) := by
  first | exact @GlobalTheory.Desc.spanBy_image_inter | exact GlobalTheory.Desc.spanBy_image_inter | (intros; apply GlobalTheory.Desc.spanBy_image_inter <;> assumption)
