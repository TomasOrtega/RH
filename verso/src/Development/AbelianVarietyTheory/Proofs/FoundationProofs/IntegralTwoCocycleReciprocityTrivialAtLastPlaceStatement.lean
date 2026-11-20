import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTwoCocycleReciprocityTrivialAtLastPlace
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ord2.Rec.reciprocity` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIntegralTwoCocycleReciprocityTrivialAtLastPlace.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.integralTwoCocycle_reciprocity_trivial_at_last_place : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (v₀ : Pl), l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → v₀ ∈ S → (∀ v ∈ S, v ≠ v₀ → ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) → ∀ B : ValuationSubring Ω, IsPlaceOver B v₀ → Cob2 c n (Dec (F := ℚ) B) ξ := by
  first | exact @GlobalTheory.Ord2.Rec.reciprocity | exact GlobalTheory.Ord2.Rec.reciprocity | (intros; apply GlobalTheory.Ord2.Rec.reciprocity <;> assumption)
