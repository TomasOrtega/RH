import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

noncomputable section

open GlobalTheory.PRep
open scoped Classical

namespace GlobalTheory.KTypeTest

variable {G : Type} [Group G] (K : Subgroup G) {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

def charFn (σ : Representation ℂ K U) (g : G) : ℂ :=
  if hg : g ∈ K then starRingEnd ℂ (LinearMap.trace ℂ U (σ ⟨g, hg⟩)) else 0

def IsKMap (σ : Representation ℂ K U) (ρ : Representation ℂ G V) (f : U →ₗ[ℂ] V) : Prop :=
  ∀ κ : K, f ∘ₗ σ κ = ρ κ ∘ₗ f

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem support_charFn (σ : Representation ℂ K U) : Function.support (charFn K σ) ⊆ (K : Set G) := by
  intro g hg
  by_contra h
  exact hg (by simp [charFn, show g ∉ K from h])

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem isKMap_zero (σ : Representation ℂ K U) (ρ : Representation ℂ G V) : IsKMap K σ ρ 0 := fun _ => by simp

end GlobalTheory.KTypeTest
