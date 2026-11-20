import Mathlib
open scoped ENNReal Classical

namespace GlobalTheory

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem tsum_transversal_eq_tsum_orbitQuotient_general {G X A M : Type} [Group G] [MulAction G X]
    [AddCommMonoid M] [TopologicalSpace M] (ι : A → X) (T : X → Prop)
    (hT : ∀ g : G, ∀ x, T x → T (g • x)) (hι : ∀ a, T (ι a))
    (hsurj : ∀ x, T x → ∃ a, ∃ g : G, g • ι a = x)
    (hinj : ∀ a b, (∃ g : G, g • ι a = ι b) → a = b)
    (φ : X → M) (hφ : ∀ g : G, ∀ x, T x → φ (g • x) = φ x) :
    ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  let c : A → MulAction.orbitRel.Quotient G X := fun a => Quotient.mk (MulAction.orbitRel G X) (ι a)
  have hc : Function.Injective c := by
    intro a b hab
    have h : (MulAction.orbitRel G X) (ι a) (ι b) := Quotient.exact hab
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨g, hg⟩ := h
    exact (hinj b a ⟨g, hg⟩).symm
  have hout : ∀ a, ∃ g : G, g • ι a = (c a).out := by
    intro a
    have h : (MulAction.orbitRel G X) ((c a).out) (ι a) := Quotient.exact (Quotient.out_eq (c a))
    rw [MulAction.orbitRel_apply] at h
    exact h
  have hsupp : Function.support
      (fun o : MulAction.orbitRel.Quotient G X => if T o.out then φ o.out else 0) ⊆ Set.range c := by
    intro o ho
    have hTo : T o.out := by
      by_contra hn
      exact ho (if_neg hn)
    obtain ⟨a, g, hg⟩ := hsurj _ hTo
    refine ⟨a, ?_⟩
    rw [← Quotient.out_eq o]
    apply Quotient.sound
    have h : (MulAction.orbitRel G X) o.out (ι a) := by
      rw [MulAction.orbitRel_apply]
      exact ⟨g, hg⟩
    exact (MulAction.orbitRel G X).symm h
  rw [← hc.tsum_eq hsupp]
  refine tsum_congr fun a => ?_
  obtain ⟨g, hg⟩ := hout a
  rw [← hg, if_pos (hT g _ (hι a)), hφ g _ (hι a)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem tsum_transversal_eq_tsum_orbitQuotient : ∀ {G X A : Type} [Group G] [MulAction G X] (ι : A → X) (T : X → Prop), (∀ g : G, ∀ x, T x → T (g • x)) → (∀ a, T (ι a)) → (∀ x, T x → ∃ a, ∃ g : G, g • ι a = x) → (∀ a b, (∃ g : G, g • ι a = ι b) → a = b) → (∀ φ : X → ℂ, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0) ∧ ∀ φ : X → ℝ≥0∞, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  intro G X A _ _ ι T hT hι hsurj hinj
  exact ⟨fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ,
    fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ⟩

end GlobalTheory
